-- Prove2me | solution 1 for ModularCurve.exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/483b5330-d9eb-5b0b-a86e-bc1a419a169e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset x1FunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem jGeomGen jNGeomGen"
namespace ConstantFieldTransport
p2m_open "ModularCurve"
namespace LegC

open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve"

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qExpand (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_jqNModC (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, jqNModC, coeffMap_qExpand, coeffMap_jqModC]

end CoeffMap

section Fields

variable {κ k : Type*} [Field κ] [Field k] (τ : κ →+* k)

theorem coeffMap_algebraMap' (c : κ) :
    coeffMap τ (algebraMap κ (LaurentSeries κ) c) = algebraMap k (LaurentSeries k) (τ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_intSeriesC (q : PowerSeries ℤ) : coeffMap τ (intSeriesC κ q) = intSeriesC k q := by
  ext n
  rw [coeffMap_coeff, intSeriesC, intSeriesC]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]

theorem coeffMap_mem_intFormRatiosC (Γ : Subgroup SL(2, ℤ)) {x : LaurentSeries κ}
    (hx : x ∈ intFormRatiosC κ Γ) : coeffMap τ x ∈ intFormRatiosC k Γ := by
  obtain ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  have hg0' : intSeriesC k pg ≠ 0 := by
    rw [← coeffMap_intSeriesC τ]; exact (map_ne_zero (coeffMap τ)).mpr hg0
  refine ⟨w, f, g, pf, pg, hf, hg, hg0', ?_⟩
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coeffMap_mem_adjoin_of_mem_adjoin {S : Set (LaurentSeries κ)} {S' : Set (LaurentSeries k)}
    (hS : ∀ x ∈ S, coeffMap τ x ∈ S') {y : LaurentSeries κ} (hy : y ∈ IntermediateField.adjoin κ S) :
    coeffMap τ y ∈ IntermediateField.adjoin k S' := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | hy
    · rw [coeffMap_algebraMap']; exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin _ _ (hS y hy)
  | one => rw [map_one]; exact IntermediateField.one_mem _
  | add y z _ _ hy hz => rw [map_add]; exact IntermediateField.add_mem _ hy hz
  | neg y _ hy => rw [map_neg]; exact IntermediateField.neg_mem _ hy
  | inv y _ hy => rw [map_inv₀]; exact IntermediateField.inv_mem _ hy
  | mul y z _ _ hy hz => rw [map_mul]; exact IntermediateField.mul_mem _ hy hz

noncomputable def restrict (F : IntermediateField κ (LaurentSeries κ)) (E : IntermediateField k (LaurentSeries k))
    (h : ∀ y : ↥F, coeffMap τ (y : LaurentSeries κ) ∈ E) : ↥F →+* ↥E :=
  RingHom.codRestrict ((coeffMap τ).comp F.toSubfield.subtype) E fun y => h y

@[scoped simp] theorem coe_restrict (F : IntermediateField κ (LaurentSeries κ)) (E : IntermediateField k (LaurentSeries k))
    (h : ∀ y : ↥F, coeffMap τ (y : LaurentSeries κ) ∈ E) (y : ↥F) :
    ((restrict τ F E h y : ↥E) : LaurentSeries k) = coeffMap τ (y : LaurentSeries κ) := rfl

theorem coeffMap_mem_modularFunctionFieldC' (M : ℕ) [NeZero M] (y : ↥(modularFunctionFieldC κ M)) :
    coeffMap τ (y : LaurentSeries κ) ∈ modularFunctionFieldC k M := by
  refine coeffMap_mem_adjoin_of_mem_adjoin τ (S := {jqModC κ, jqNModC κ M}) ?_ y.2
  intro x hx
  rcases hx with rfl | hx
  · rw [coeffMap_jqModC]; exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff] at hx; subst hx
    rw [coeffMap_jqNModC]; exact Set.mem_insert_of_mem _ rfl

theorem coeffMap_mem_x1FunctionFieldC (M : ℕ) (y : ↥(x1FunctionFieldC κ M)) :
    coeffMap τ (y : LaurentSeries κ) ∈ x1FunctionFieldC k M :=
  coeffMap_mem_adjoin_of_mem_adjoin τ (fun _ hx => coeffMap_mem_intFormRatiosC τ _ hx) y.2

end Fields

section AdjoinTop

variable {k X F : Type*} [Field k] [Field X] [Algebra k X] [Field F]

theorem adjoin_range_eq_top (E : IntermediateField k X) (S : Set X) (hE : E ≤ IntermediateField.adjoin k S)
    (L : F →+* ↥E) (hS : ∀ s ∈ S, ∃ y : F, ((L y : ↥E) : X) = s)
    (hint : ∀ c : k, ∃ q : Polynomial F, q.Monic ∧ Polynomial.eval₂ L (algebraMap k ↥E c) q = 0) :
    Algebra.adjoin k (Set.range L) = ⊤ := by
  classical
  letI : Algebra F ↥E := L.toAlgebra

  set R : Subalgebra F ↥E := Algebra.adjoin F (Set.range (algebraMap k ↥E)) with hR
  have hRint : Algebra.IsIntegral F ↥R := by
    rw [← le_integralClosure_iff_isIntegral]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, mem_integralClosure_iff]
    obtain ⟨q, hq, hq0⟩ := hint c
    exact ⟨q, hq, hq0⟩
  have hRinv : ∀ x : ↥E, x ∈ R → x⁻¹ ∈ R := by
    intro x hx
    have h1 : IsIntegral F (⟨x, hx⟩ : ↥R) := hRint.isIntegral _
    have h2 : IsIntegral F (R.val (⟨x, hx⟩ : ↥R)) := h1.map R.val
    exact Subalgebra.inv_mem_of_algebraic R (x := ⟨x, hx⟩) h2.isAlgebraic

  have hmem : ∀ x : ↥E, x ∈ Algebra.adjoin k (Set.range L) ↔ x ∈ R := by
    intro x
    rw [Algebra.mem_adjoin_iff, hR, Algebra.mem_adjoin_iff, RingHom.algebraMap_toAlgebra, Set.union_comm]

  let T : IntermediateField k X :=
    { toSubalgebra := (Algebra.adjoin k (Set.range L)).map E.val
      inv_mem' := by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := Subalgebra.mem_map.mp hx
        have hr' : r⁻¹ ∈ Algebra.adjoin k (Set.range L) := (hmem _).mpr (hRinv r ((hmem r).mp hr))
        refine Subalgebra.mem_map.mpr ⟨r⁻¹, hr', ?_⟩
        simp }
  have hST : S ⊆ (T : Set X) := by
    intro s hs
    obtain ⟨y, hy⟩ := hS s hs
    show s ∈ (Algebra.adjoin k (Set.range L)).map E.val
    exact Subalgebra.mem_map.mpr ⟨L y, Algebra.subset_adjoin ⟨y, rfl⟩, hy⟩
  have hET : E ≤ T := hE.trans (IntermediateField.adjoin_le_iff.mpr hST)
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (x : X) ∈ T := hET x.2
  obtain ⟨r, hr, hrx⟩ := Subalgebra.mem_map.mp (show (x : X) ∈ (Algebra.adjoin k (Set.range L)).map E.val from hx)
  have : r = x := Subtype.ext (by simpa using hrx)
  exact this ▸ hr

theorem exists_monic_eval₂_eq_zero_of_pow_eq (p : ℕ) [Fact p.Prime]
    (halg : ∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x)
    {E : Type*} [Field E] [Algebra k E] (L : F →+* E) (c : k) :
    ∃ q : Polynomial F, q.Monic ∧ Polynomial.eval₂ L (algebraMap k E c) q = 0 := by
  obtain ⟨n, hn, hc⟩ := halg c
  have hlt : 1 < p ^ n := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.X, ?_, ?_⟩
  · refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
    rw [Polynomial.degree_X_pow, Polynomial.degree_X]
    exact_mod_cast hlt
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, ← map_pow, hc, sub_self]

end AdjoinTop

section Transport

variable {F₀ F₁ E₀ E₁ : Type*} [Field F₀] [Field F₁] [Field E₀] [Field E₁] [Algebra F₀ F₁] [Algebra E₀ E₁]

theorem finiteDimensional_and_isSeparable_of_forall_eq_top [FiniteDimensional F₀ F₁] [Algebra.IsSeparable F₀ F₁]
    (Lθ : F₀ →+* E₀) (Lφ : F₁ →+* E₁) (hcomm : ∀ x : F₀, Lφ (algebraMap F₀ F₁ x) = algebraMap E₀ E₁ (Lθ x))
    (hgen : ∀ T : IntermediateField E₀ E₁, (∀ y : F₁, Lφ y ∈ T) → T = ⊤) :
    FiniteDimensional E₀ E₁ ∧ Algebra.IsSeparable E₀ E₁ := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := F₀) (M := F₁)
  set T : IntermediateField E₀ E₁ := IntermediateField.adjoin E₀ (Set.range fun i => Lφ (s i)) with hT
  have hcomp : (algebraMap E₀ E₁).comp Lθ = Lφ.comp (algebraMap F₀ F₁) := RingHom.ext fun x => (hcomm x).symm
  have hroot : ∀ i, Polynomial.aeval (Lφ (s i)) ((minpoly F₀ (s i)).map Lθ) = 0 := by
    intro i
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      minpoly.aeval, map_zero]
  have hint : ∀ i, IsIntegral E₀ (Lφ (s i)) := fun i =>
    ⟨(minpoly F₀ (s i)).map Lθ, (minpoly.monic (IsIntegral.of_finite F₀ (s i))).map Lθ,
      by rw [← Polynomial.aeval_def]; exact hroot i⟩
  have hsep : ∀ i, IsSeparable E₀ (Lφ (s i)) := fun i => by
    have h0 : (minpoly F₀ (s i)).Separable := Algebra.IsSeparable.isSeparable F₀ (s i)
    have h1 : ((minpoly F₀ (s i)).map Lθ).Separable := h0.map
    exact h1.of_dvd (minpoly.dvd E₀ _ (hroot i))
  haveI hTfin : FiniteDimensional E₀ ↥T :=
    IntermediateField.finiteDimensional_adjoin fun x hx => by obtain ⟨i, rfl⟩ := hx; exact hint i
  haveI hTsep : Algebra.IsSeparable E₀ ↥T :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable E₀ E₁).mpr fun x hx => by obtain ⟨i, rfl⟩ := hx; exact hsep i
  have hyT : ∀ y : F₁, Lφ y ∈ T := by
    intro y
    have hy : y ∈ Submodule.span F₀ (Set.range s) := by rw [hs]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | zero => rw [map_zero]; exact T.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact T.add_mem hy hz
    | smul c y _ hy =>
      rw [Algebra.smul_def, map_mul, hcomm]
      exact T.mul_mem (T.algebraMap_mem _) hy
  have hTtop : T = ⊤ := hgen T hyT
  let e : ↥T ≃ₐ[E₀] E₁ := (IntermediateField.equivOfEq hTtop).trans IntermediateField.topEquiv
  exact ⟨LinearEquiv.finiteDimensional e.toLinearEquiv, Algebra.IsSeparable.of_algHom E₀ ↥T e.symm.toAlgHom⟩

end Transport

end LegC
p2m_reactivate "P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve.ConstantFieldTransport.LegC"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem _root_.P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (κ k : Type) [Field κ] [CharP κ p] [Field k] [CharP k p] [IsAlgClosed k]
    (halg : ∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x)
    (τ : κ →+* k)
    (hincl : ModularCurve.modularFunctionFieldC κ M ≤ ModularCurve.x1FunctionFieldC κ M)
    (hfin : letI := (IntermediateField.inclusion hincl).toRingHom.toAlgebra;
      FiniteDimensional ↥(ModularCurve.modularFunctionFieldC κ M) ↥(ModularCurve.x1FunctionFieldC κ M) ∧
      Algebra.IsSeparable ↥(ModularCurve.modularFunctionFieldC κ M) ↥(ModularCurve.x1FunctionFieldC κ M)) :
    ∃ (Lθ : ↥(ModularCurve.modularFunctionFieldC κ M) →+* ↥(ModularCurve.modularFunctionFieldC k M))
      (Lφ : ↥(ModularCurve.x1FunctionFieldC κ M) →+* ↥(ModularCurve.x1FunctionFieldC k M))
      (hincl' : ModularCurve.modularFunctionFieldC k M ≤ ModularCurve.x1FunctionFieldC k M),
      (∀ f, ((Lθ f : ↥(ModularCurve.modularFunctionFieldC k M)) : LaurentSeries k) =
        ModularCurve.coeffMap τ ((f : ↥(ModularCurve.modularFunctionFieldC κ M)) : LaurentSeries κ)) ∧
      (∀ f, ((Lφ f : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) =
        ModularCurve.coeffMap τ ((f : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ)) ∧
      (∀ c : κ, Lθ (algebraMap κ _ c) = algebraMap k _ (τ c)) ∧
      (∀ c : κ, Lφ (algebraMap κ _ c) = algebraMap k _ (τ c)) ∧
      Lθ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M ∧
      Lθ (ModularCurve.jNGeomGen κ M) = ModularCurve.jNGeomGen k M ∧
      Algebra.adjoin k (Set.range Lθ) = ⊤ ∧ Algebra.adjoin k (Set.range Lφ) = ⊤ ∧
      (letI := (IntermediateField.inclusion hincl').toRingHom.toAlgebra;
        FiniteDimensional ↥(ModularCurve.modularFunctionFieldC k M) ↥(ModularCurve.x1FunctionFieldC k M) ∧
        Algebra.IsSeparable ↥(ModularCurve.modularFunctionFieldC k M) ↥(ModularCurve.x1FunctionFieldC k M)) := by
  classical

  let Lθ : ↥(modularFunctionFieldC κ M) →+* ↥(modularFunctionFieldC k M) :=
    LegC.restrict τ _ _ (LegC.coeffMap_mem_modularFunctionFieldC' τ M)
  let Lφ : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC k M) :=
    LegC.restrict τ _ _ (LegC.coeffMap_mem_x1FunctionFieldC τ M)
  have hLθ : ∀ f, ((Lθ f : ↥(modularFunctionFieldC k M)) : LaurentSeries k) = coeffMap τ (f : LaurentSeries κ) :=
    fun _ => rfl
  have hLφ : ∀ f, ((Lφ f : ↥(x1FunctionFieldC k M)) : LaurentSeries k) = coeffMap τ (f : LaurentSeries κ) :=
    fun _ => rfl

  have hjκ : jqModC κ ∈ x1FunctionFieldC κ M := hincl (jqModC_mem κ M)
  have hjNκ : jqNModC κ M ∈ x1FunctionFieldC κ M := hincl (jqNModC_mem κ M)
  have hjk : jqModC k ∈ x1FunctionFieldC k M := by
    simpa only [LegC.coeffMap_jqModC] using LegC.coeffMap_mem_x1FunctionFieldC τ M ⟨jqModC κ, hjκ⟩
  have hjNk : jqNModC k M ∈ x1FunctionFieldC k M := by
    simpa only [LegC.coeffMap_jqNModC] using LegC.coeffMap_mem_x1FunctionFieldC τ M ⟨jqNModC κ M, hjNκ⟩
  have hincl' : modularFunctionFieldC k M ≤ x1FunctionFieldC k M := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hjk
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hjNk

  have hLθκ : ∀ c : κ, Lθ (algebraMap κ _ c) = algebraMap k _ (τ c) := fun c =>
    Subtype.ext (by rw [hLθ]; exact LegC.coeffMap_algebraMap' τ c)
  have hLφκ : ∀ c : κ, Lφ (algebraMap κ _ c) = algebraMap k _ (τ c) := fun c =>
    Subtype.ext (by rw [hLφ]; exact LegC.coeffMap_algebraMap' τ c)

  have hLθj : Lθ (jGeomGen κ M) = jGeomGen k M :=
    Subtype.ext (by rw [hLθ]; exact LegC.coeffMap_jqModC τ)
  have hLθjN : Lθ (jNGeomGen κ M) = jNGeomGen k M :=
    Subtype.ext (by rw [hLθ]; exact LegC.coeffMap_jqNModC τ M)

  have hgenθ : Algebra.adjoin k (Set.range Lθ) = ⊤ := by
    refine LegC.adjoin_range_eq_top (modularFunctionFieldC k M) {jqModC k, jqNModC k M} le_rfl Lθ ?_
      (LegC.exists_monic_eval₂_eq_zero_of_pow_eq p halg Lθ)
    intro s hs
    rcases hs with rfl | hs
    · exact ⟨⟨jqModC κ, jqModC_mem κ M⟩, by rw [hLθ]; exact LegC.coeffMap_jqModC τ⟩
    · rw [Set.mem_singleton_iff] at hs; subst hs
      exact ⟨⟨jqNModC κ M, jqNModC_mem κ M⟩, by rw [hLθ]; exact LegC.coeffMap_jqNModC τ M⟩
  have hgenφ : Algebra.adjoin k (Set.range Lφ) = ⊤ := by
    refine LegC.adjoin_range_eq_top (x1FunctionFieldC k M) (intFormRatiosC k (CongruenceSubgroup.Gamma1 M)) le_rfl Lφ ?_
      (LegC.exists_monic_eval₂_eq_zero_of_pow_eq p halg Lφ)
    rintro s ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hg0' : intSeriesC κ pg ≠ 0 := by
      intro h; apply hg0; rw [← LegC.coeffMap_intSeriesC τ, h, map_zero]
    refine ⟨⟨intSeriesC κ pf / intSeriesC κ pg, ?_⟩, ?_⟩
    · exact intFormRatiosC_subset κ _ ⟨w, f, g, pf, pg, hf, hg, hg0', rfl⟩
    · rw [hLφ, map_div₀, LegC.coeffMap_intSeriesC, LegC.coeffMap_intSeriesC]

  have hfink : letI := (IntermediateField.inclusion hincl').toRingHom.toAlgebra;
      FiniteDimensional ↥(modularFunctionFieldC k M) ↥(x1FunctionFieldC k M) ∧
      Algebra.IsSeparable ↥(modularFunctionFieldC k M) ↥(x1FunctionFieldC k M) := by
    letI := (IntermediateField.inclusion hincl).toRingHom.toAlgebra
    letI := (IntermediateField.inclusion hincl').toRingHom.toAlgebra
    obtain ⟨hfd, hsp⟩ := hfin
    refine LegC.finiteDimensional_and_isSeparable_of_forall_eq_top Lθ Lφ (fun x => rfl) ?_
    intro T hT
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ Algebra.adjoin k (Set.range Lφ) := by rw [hgenφ]; exact Algebra.mem_top
    rw [Algebra.mem_adjoin_iff] at hx
    have hle : Subring.closure (Set.range (algebraMap k ↥(x1FunctionFieldC k M)) ∪ Set.range Lφ) ≤
        T.toSubfield.toSubring := by
      refine Subring.closure_le.mpr ?_
      rintro y (⟨c, rfl⟩ | ⟨z, rfl⟩)
      · exact T.algebraMap_mem (algebraMap k ↥(modularFunctionFieldC k M) c)
      · exact hT z
    exact hle hx
  exact ⟨Lθ, Lφ, hincl', hLθ, hLφ, hLθκ, hLφκ, hLθj, hLθjN, hgenθ, hgenφ, hfink⟩

end ModularCurve.ConstantFieldTransport
p2m_reactivate "P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve.ConstantFieldTransport.LegC P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve.ConstantFieldTransport"
p2m_reactivate "P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve.ConstantFieldTransport.LegC P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq.ModularCurve"

end S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_modularFunctionFieldC_x1FunctionFieldC_coe_eq_coeffMap_of_forall_exists_pow_eq (solution)
