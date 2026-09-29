-- Prove2me | solution 1 for ModularCurve.XOneP.exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bd533ae0-16f6-54dc-a7de-2e0b9f1e0150

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open AlgebraicCurve Polynomial

noncomputable section

namespace K1CA

def CoeffsIn {Λ : Type*} [CommRing Λ] (T : Subring Λ) (f : Polynomial Λ) : Prop := ∀ n, f.coeff n ∈ T

namespace CoeffsIn
variable {Λ : Type*} [CommRing Λ] {T : Subring Λ}

theorem iff_mem_lifts (f : Polynomial Λ) : CoeffsIn T f ↔ f ∈ Polynomial.lifts T.subtype := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  refine forall_congr' fun n => ?_
  constructor
  · intro h; exact ⟨⟨_, h⟩, rfl⟩
  · rintro ⟨x, hx⟩; rw [← hx]; exact x.2

theorem C_mem {x : Λ} (hx : x ∈ T) : CoeffsIn T (Polynomial.C x) := fun n => by
  rw [Polynomial.coeff_C]; split_ifs <;> [exact hx; exact T.zero_mem]

theorem X_mem : CoeffsIn T (Polynomial.X : Polynomial Λ) := fun n => by
  rw [Polynomial.coeff_X]; split_ifs <;> [exact T.one_mem; exact T.zero_mem]

theorem add {f g : Polynomial Λ} (hf : CoeffsIn T f) (hg : CoeffsIn T g) : CoeffsIn T (f + g) := by
  rw [iff_mem_lifts] at *; exact Subsemiring.add_mem _ hf hg

theorem mul {f g : Polynomial Λ} (hf : CoeffsIn T f) (hg : CoeffsIn T g) : CoeffsIn T (f * g) := by
  rw [iff_mem_lifts] at *; exact Subsemiring.mul_mem _ hf hg

theorem neg {f : Polynomial Λ} (hf : CoeffsIn T f) : CoeffsIn T (-f) := fun n => by
  rw [Polynomial.coeff_neg]; exact T.neg_mem (hf n)

theorem sub {f g : Polynomial Λ} (hf : CoeffsIn T f) (hg : CoeffsIn T g) : CoeffsIn T (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem one : CoeffsIn T (1 : Polynomial Λ) := by simpa using C_mem (T := T) T.one_mem

theorem prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial Λ) (h : ∀ i ∈ s, CoeffsIn T (f i)) :
    CoeffsIn T (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : CoeffsIn T 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial Λ) (h : ∀ i ∈ s, CoeffsIn T (f i)) :
    CoeffsIn T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n; simp [T.zero_mem]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CoeffsIn

theorem isIntegral_subring_iff {Λ : Type*} [CommRing Λ] [Nontrivial Λ] (T : Subring Λ) (x : Λ) :
    IsIntegral T x ↔ ∃ P : Polynomial Λ, P.Monic ∧ CoeffsIn T P ∧ P.eval x = 0 := by
  constructor
  · rintro ⟨P, hP, hx⟩
    refine ⟨P.map T.subtype, hP.map _, fun n => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (P.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨P, hP, hT, hx⟩
    have hl : P ∈ Polynomial.lifts T.subtype := (CoeffsIn.iff_mem_lifts P).mp hT
    obtain ⟨Q, hQmap, -, hQmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hP
    refine ⟨Q, hQmon, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval x (Q.map T.subtype) = 0
    rw [hQmap]; exact hx

theorem isIntegral_map_subring_iff {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] [Nontrivial Λ] [Nontrivial Λ'] (φ : Λ →+* Λ') (hφ : Function.Injective φ)
    (T : Subring Λ) (x : Λ) : IsIntegral ↥(T.map φ) (φ x) ↔ IsIntegral ↥T x := by
  constructor
  · intro h
    obtain ⟨P, hP, hT, hx⟩ := (isIntegral_subring_iff _ _).mp h
    have hl : P ∈ Polynomial.lifts (φ.comp T.subtype) := by
      rw [Polynomial.lifts_iff_coeff_lifts]; intro n
      obtain ⟨t, ht, htn⟩ := Subring.mem_map.mp (hT n)
      exact ⟨⟨t, ht⟩, htn⟩
    obtain ⟨Q, hQmap, -, hQmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hP
    refine ⟨Q, hQmon, hφ ?_⟩
    rw [map_zero, Polynomial.hom_eval₂]
    change Polynomial.eval₂ (φ.comp T.subtype) (φ x) Q = 0
    rw [← Polynomial.eval_map, hQmap]; exact hx
  · rintro ⟨P, hP, hx⟩
    refine (isIntegral_subring_iff _ _).mpr ⟨(P.map T.subtype).map φ, (hP.map _).map _, fun n => ?_, ?_⟩
    · rw [Polynomial.coeff_map, Polynomial.coeff_map]; exact Subring.mem_map.mpr ⟨_, (P.coeff n).2, rfl⟩
    · rw [Polynomial.eval_map, Polynomial.eval₂_map, ← Polynomial.hom_eval₂]
      change φ (Polynomial.eval₂ (algebraMap (↥T) Λ) x P) = 0
      rw [hx, map_zero]

theorem isIntegral_coeff_prod_X_sub_C {Λ : Type*} [CommRing Λ] (T : Subring Λ) {ι : Type*} (s : Finset ι) (t : ι → Λ)
    (ht : ∀ i ∈ s, IsIntegral ↥T (t i)) (n : ℕ) : IsIntegral ↥T ((∏ i ∈ s, (Polynomial.X - Polynomial.C (t i))).coeff n) := by

  let S : Subring Λ := (integralClosure (↥T) Λ).toSubring
  have hS : CoeffsIn S (∏ i ∈ s, (Polynomial.X - Polynomial.C (t i))) :=
    CoeffsIn.prod s _ fun i hi => CoeffsIn.X_mem.sub (CoeffsIn.C_mem (ht i hi))
  exact hS n

theorem isIntegral_subalgebra_iff {A Λ : Type*} [CommRing A] [CommRing Λ] [Nontrivial Λ] [Algebra A Λ]
    (T : Subalgebra A Λ) (x : Λ) :
    IsIntegral T x ↔ ∃ P : Polynomial Λ, P.Monic ∧ CoeffsIn T.toSubring P ∧ P.eval x = 0 := by
  constructor
  · rintro ⟨P, hP, hx⟩
    refine ⟨P.map (algebraMap T Λ), hP.map _, fun n => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (P.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨P, hP, hT, hx⟩
    have hl : P ∈ Polynomial.lifts (algebraMap T Λ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]; intro n; exact ⟨⟨_, hT n⟩, rfl⟩
    obtain ⟨Q, hQmap, -, hQmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hP
    refine ⟨Q, hQmon, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hQmap]; exact hx

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) :
    ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand S n (ModularCurve.coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul,
      ModularCurve.coeffMap_coeff]
  · rw [ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd n _ hk,
      ModularCurve.qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) :=
  coeffMap_qExpand _ n x

end K1CA

open K1CA

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_qExpand" in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hβdef : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hdeg : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L (M * p) p) = p)
    (g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ E : Polynomial ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      E.Monic ∧ E.natDegree = p ∧
      E.map ((ModularCurve.qExpand L p).comp
          ((algebraMap ↥K (LaurentSeries L)).comp
            (algebraMap ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ↥K))) =
        ∏ i : Fin p, (Polynomial.X - Polynomial.C
          (ModularCurve.qTwist (ζ ^ (i : ℕ)) (((g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let Λ := LaurentSeries L
  let R := ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)
  let t : Fin p → Λ := fun i => ModularCurve.qTwist (ζ ^ (i : ℕ)) ((g : ↥K) : Λ)
  let Pw : Polynomial Λ := ∏ i : Fin p, (Polynomial.X - Polynomial.C (t i))
  let Fb := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
  let Ft := ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))
  let α : Fb →ₐ[L] Ft := ModularCurve.heckeAlphaOneBar L (M * p) p
  let β : Fb →ₐ[L] Ft := ModularCurve.heckeBetaOneBar L (M * p) p
  let qE : Λ →+* Λ := ModularCurve.qExpand L p
  have hjΛ : ((j : ↥K) : Λ) = ModularCurve.jqModC L := by
    rw [hj, ModularCurve.coeffEmb, ← ModularCurve.jqModC_rat]; exact ModularCurve.map_jqModC _
  have hF : ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) := by
    rw [← hjΛ, ← hK]; exact j.2
  have hgmem : ((g : ↥K) : Λ) ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) := by
    rw [← hK]; exact (g : ↥K).2
  let gF : Fb := ⟨_, hgmem⟩

  let F0 : Subfield Λ := K.toSubfield.map qE
  have hmemF0 : ∀ z : Λ, z ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) → qE z ∈ F0 := by
    intro z hz
    exact Subfield.mem_map.mpr ⟨z, by rw [IntermediateField.mem_toSubfield, hK]; exact hz, rfl⟩
  have hconstF0 : ∀ c : L, algebraMap L Λ c ∈ F0 := by
    intro c
    have : qE (algebraMap L Λ c) = algebraMap L Λ c := by
      change ModularCurve.qExpand L p _ = _
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.qExpand_single, mul_zero]
    rw [← this]
    exact Subfield.mem_map.mpr ⟨_, by rw [IntermediateField.mem_toSubfield]; exact K.algebraMap_mem c, rfl⟩
  have hval : ∀ c : L, Pw.eval (algebraMap L Λ c) ∈ F0 := by
    intro c
    letI := algebraAlong β
    let y : Ft := α gF - algebraMap L Ft c
    have hK1a := ModularCurve.coe_heckeBetaOneBar_norm_eq_prod_qTwist_of_finrankAlong_eq L (M * p) p hF hβdef hdeg ζ hζ y
    have hy : (y : Λ) = ((g : ↥K) : Λ) - algebraMap L Λ c := by
      change ((α gF : Ft) : Λ) - ((algebraMap L Ft c : Ft) : Λ) = _
      rw [ModularCurve.coe_heckeAlphaOneBar]; rfl
    have htw : ∀ i : Fin p, ModularCurve.qTwist (ζ ^ (i : ℕ)) (y : Λ) = t i - algebraMap L Λ c := by
      intro i
      rw [hy, map_sub, ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.qTwist_single, zpow_zero, Units.val_one, one_mul]
    have hev : Pw.eval (algebraMap L Λ c) = (-1) ^ p * ∏ i : Fin p, ModularCurve.qTwist (ζ ^ (i : ℕ)) (y : Λ) := by
      change Polynomial.eval (algebraMap L Λ c) (∏ i : Fin p, (Polynomial.X - Polynomial.C (t i))) = _
      rw [Polynomial.eval_prod]
      have : ∀ i ∈ (Finset.univ : Finset (Fin p)), Polynomial.eval (algebraMap L Λ c) (Polynomial.X - Polynomial.C (t i)) =
          (-1) * ModularCurve.qTwist (ζ ^ (i : ℕ)) (y : Λ) := by
        intro i _; rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, htw, neg_one_mul, neg_sub]
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hev, ← hK1a, ModularCurve.coe_heckeBetaOneBar _ _ hβdef]
    exact F0.mul_mem (F0.pow_mem (F0.neg_mem F0.one_mem) p) (hmemF0 _ (Algebra.norm Fb y).2)

  have hPwdeg : Pw.natDegree = p := by
    change (∏ i : Fin p, (Polynomial.X - Polynomial.C (t i))).natDegree = p
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  have hPwmon : Pw.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (t i)
  have hcoeffF0 : ∀ n, Pw.coeff n ∈ F0 := by
    let v : Fin (p + 1) → Λ := fun m => algebraMap L Λ ((m : ℕ) : L)
    have hv : Set.InjOn v (Finset.univ : Finset (Fin (p + 1))) := by
      intro a _ b _ h
      have h' := (algebraMap L Λ).injective h
      exact Fin.ext (Nat.cast_injective (R := L) h')
    have hlt : Pw.degree < (Finset.univ : Finset (Fin (p + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin, Polynomial.degree_eq_natDegree hPwmon.ne_zero, hPwdeg]
      exact_mod_cast Nat.lt_succ_self p
    have hPweq := Lagrange.eq_interpolate (s := Finset.univ) (v := v) hv hlt
    have hCo : CoeffsIn F0.toSubring (Lagrange.interpolate Finset.univ v fun m => Pw.eval (v m)) := by
      rw [Lagrange.interpolate_apply]
      refine CoeffsIn.sum _ _ fun m _ => (CoeffsIn.C_mem (hval _)).mul ?_
      change CoeffsIn F0.toSubring (∏ m' ∈ Finset.univ.erase m, Lagrange.basisDivisor (v m) (v m'))
      refine CoeffsIn.prod _ _ fun m' _ => ?_
      change CoeffsIn F0.toSubring (Polynomial.C ((v m - v m')⁻¹) * (Polynomial.X - Polynomial.C (v m')))
      exact (CoeffsIn.C_mem (F0.inv_mem (F0.sub_mem (hconstF0 _) (hconstF0 _)))).mul
        (CoeffsIn.X_mem.sub (CoeffsIn.C_mem (hconstF0 _)))
    intro n
    rw [hPweq]; exact hCo n

  let ιK : ↥K →+* Λ := algebraMap (↥K) Λ
  let T₀ : Subring Λ := (Algebra.adjoin A ({j} : Set ↥K)).toSubring.map ιK
  let B : Subring Λ := T₀.map qE
  have hιK : Function.Injective ιK := (algebraMap (↥K) Λ).injective
  have hqE : Function.Injective qE := ModularCurve.qExpand_injective (R := L) (N := p)

  let τ : Fin p → (Λ →+* Λ) := fun i => ModularCurve.qTwist (ζ ^ (i : ℕ))
  have hζp : ζ ^ p = 1 := (IsPrimitiveRoot.coe_units_iff.mp hζ).pow_eq_one
  have hτqE : ∀ (i : Fin p) (x : Λ), τ i (qE x) = qE x := by
    intro i x
    change ModularCurve.qTwist (ζ ^ (i : ℕ)) (ModularCurve.qExpand L p x) = ModularCurve.qExpand L p x
    rw [ModularCurve.qTwist_qExpand, zpow_natCast, ← pow_mul, mul_comm (i : ℕ) p, pow_mul, hζp, one_pow,
      ModularCurve.qTwist_one_apply]
  have hτconst : ∀ (i : Fin p) (c : L), τ i (algebraMap L Λ c) = algebraMap L Λ c := by
    intro i c
    change ModularCurve.qTwist (ζ ^ (i : ℕ)) (algebraMap L (LaurentSeries L) c) = _
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.qTwist_single, zpow_zero, Units.val_one, one_mul]

  have hjT₀ : ((j : ↥K) : Λ) ∈ T₀ := Subring.mem_map.mpr ⟨j, Algebra.self_mem_adjoin_singleton A j, rfl⟩
  have hqjB : qE ((j : ↥K) : Λ) ∈ B := Subring.mem_map.mpr ⟨_, hjT₀, rfl⟩
  have hAT₀ : ∀ a : A, algebraMap L Λ (algebraMap A L a) ∈ T₀ := fun a =>
    Subring.mem_map.mpr ⟨algebraMap A (↥K) a, (Algebra.adjoin A ({j} : Set ↥K)).algebraMap_mem a, by
      rw [IsScalarTower.algebraMap_apply A L (↥K) a]; rfl⟩
  have hAB : ∀ a : A, algebraMap L Λ (algebraMap A L a) ∈ B := fun a =>
    Subring.mem_map.mpr ⟨_, hAT₀ a, by
      change ModularCurve.qExpand L p (algebraMap L (LaurentSeries L) (algebraMap A L a)) = _
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.qExpand_single, mul_zero]⟩

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  have hsymm := ModularCurve.ModularPolynomialData.evalSymm_of_one_lt p (Fact.out : p.Prime).one_lt data
  let θ : Polynomial ℤ →+* Λ :=
    (ModularCurve.coeffEmb L).comp (Polynomial.aeval (R := ℤ) (ModularCurve.jqN p)).toRingHom
  have hθX : θ Polynomial.X = qE ((j : ↥K) : Λ) := by
    change ModularCurve.coeffEmb L (Polynomial.aeval (R := ℤ) (ModularCurve.jqN p) Polynomial.X) = _
    rw [Polynomial.aeval_X, ModularCurve.jqN, coeffEmb_qExpand, ← hj]
  have hθmem : ∀ c : Polynomial ℤ, θ c ∈ B := by
    intro c
    refine Polynomial.induction_on c (fun a => ?_) (fun f₁ f₂ h₁ h₂ => ?_) (fun n a ih => ?_)
    · have : θ (Polynomial.C a) = (a : Λ) := eq_intCast (θ.comp Polynomial.C) a
      rw [this]; exact intCast_mem B a
    · rw [map_add]; exact add_mem h₁ h₂
    · rw [pow_succ, ← mul_assoc, map_mul, hθX]; exact mul_mem ih hqjB
  have hPco : CoeffsIn B (data.Φ.map θ) := fun n => by rw [Polynomial.coeff_map]; exact hθmem _
  have hP0 : data.Φ.eval₂ θ ((j : ↥K) : Λ) = 0 := by
    have h0 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqN p)).toRingHom ModularCurve.jq = 0 := by
      rw [← hsymm]; exact data.eval_eq_zero
    have := congrArg (ModularCurve.coeffEmb L) h0
    rw [map_zero, Polynomial.hom_eval₂, ← hj] at this
    exact this
  have hτθ : ∀ i : Fin p, (τ i).comp θ = θ := by
    intro i
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext_int
    · change τ i (θ Polynomial.X) = θ Polynomial.X
      rw [hθX, hτqE]
  have hProot : ∀ i : Fin p, (data.Φ.map θ).eval (τ i ((j : ↥K) : Λ)) = 0 := by
    intro i
    rw [Polynomial.eval_map, ← hτθ i, ← Polynomial.hom_eval₂, hP0, map_zero]
  have hint_j : ∀ i : Fin p, IsIntegral ↥B (τ i ((j : ↥K) : Λ)) := fun i =>
    (isIntegral_subring_iff B _).mpr ⟨_, data.monic.map θ, hPco, hProot i⟩

  have hgen : ∀ (i : Fin p), ∀ y ∈ (⇑((τ i).comp ιK)) '' (Set.range (algebraMap A ↥K) ∪ {j}), IsIntegral ↥B y := by
    rintro i _ ⟨x, hx, rfl⟩
    rcases hx with ⟨a, rfl⟩ | hx
    · have : ((τ i).comp ιK) (algebraMap A (↥K) a) = algebraMap L Λ (algebraMap A L a) := by
        change τ i (ιK (algebraMap A (↥K) a)) = _
        rw [IsScalarTower.algebraMap_apply A L (↥K) a]
        exact hτconst i _
      rw [this]
      exact isIntegral_algebraMap (R := ↥B) (x := (⟨_, hAB a⟩ : ↥B))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hint_j i
  have hSi : ∀ (i : Fin p), ∀ y ∈ (Algebra.adjoin A ({j} : Set ↥K)).toSubring.map ((τ i).comp ιK),
      IsIntegral ↥B y := by
    intro i y hy
    rw [Algebra.adjoin_eq_ring_closure, RingHom.map_closure] at hy
    exact IsIntegral.of_mem_closure' _ (hgen i) y hy

  have hgS : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)) (g : ↥K) :=
    (ModularCurve.TwoChart.mem_chartAlg_iff A (↥K)).mp g.2
  have hgS' : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)).toSubring (g : ↥K) :=
    (isIntegral_subring_iff _ _).mpr ((isIntegral_subalgebra_iff _ _).mp hgS)
  have ht : ∀ i : Fin p, IsIntegral ↥B (t i) := by
    intro i
    have h1 : IsIntegral ↥((Algebra.adjoin A ({j} : Set ↥K)).toSubring.map ((τ i).comp ιK)) (t i) :=
      (isIntegral_map_subring_iff ((τ i).comp ιK) ((τ i).injective.comp hιK) _ (g : ↥K)).mpr hgS'
    obtain ⟨Q, hQmon, hQco, hQev⟩ := (isIntegral_subring_iff _ _).mp h1
    have hQC : CoeffsIn (integralClosure ↥B Λ).toSubring Q := fun n => hSi i _ (hQco n)
    have h2 : IsIntegral ↥(integralClosure ↥B Λ).toSubring (t i) :=
      (isIntegral_subring_iff _ _).mpr ⟨Q, hQmon, hQC, hQev⟩
    obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp h2
    rw [← hc]
    exact c.2
  have hcoeffB : ∀ n, IsIntegral ↥B (Pw.coeff n) := fun n =>
    isIntegral_coeff_prod_X_sub_C B Finset.univ t (fun i _ => ht i) n

  have hrange : ∀ n, Pw.coeff n ∈ Set.range (qE.comp (ιK.comp (algebraMap R ↥K))) := by
    intro n
    obtain ⟨z, hzK, hz⟩ := Subfield.mem_map.mp (hcoeffF0 n)
    rw [IntermediateField.mem_toSubfield] at hzK
    have hzB : IsIntegral ↥B (qE z) := by rw [hz]; exact hcoeffB n
    have hzT : IsIntegral ↥T₀ z := (isIntegral_map_subring_iff qE hqE T₀ z).mp hzB
    let e : ↥K := ⟨z, hzK⟩
    have heT : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)).toSubring e :=
      (isIntegral_map_subring_iff ιK hιK (Algebra.adjoin A ({j} : Set ↥K)).toSubring e).mp hzT
    have heR : (e : ↥K) ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j :=
      (ModularCurve.TwoChart.mem_chartAlg_iff A (↥K)).mpr
        ((isIntegral_subalgebra_iff _ _).mpr ((isIntegral_subring_iff _ _).mp heT))
    exact ⟨⟨e, heR⟩, hz⟩
  have hlifts : Pw ∈ Polynomial.lifts (qE.comp (ιK.comp (algebraMap R ↥K))) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr hrange
  obtain ⟨E, hEmap, hEdeg, hEmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hPwmon
  exact ⟨E, hEmon, hEdeg.trans hPwdeg, hEmap⟩

end

end S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul (solution)
