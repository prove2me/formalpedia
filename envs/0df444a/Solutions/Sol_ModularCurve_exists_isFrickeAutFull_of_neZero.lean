-- Prove2me | solution 1 for ModularCurve.exists_isFrickeAutFull_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4adabde3-44c7-5ef2-b008-6553638a7331

import Mathlib
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "Polynomial IntermediateField ModularCurve~coeffEmb_qExpand~coeffEmb_injective ModularCurve.PhiGen AlgebraicCurve"

noncomputable section

namespace FrickeGeneral

abbrev evX {R : Type*} [CommRing R] (x : R) : Polynomial ℤ →+* R :=
  Polynomial.eval₂RingHom (Int.castRingHom R) x

def ev {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (x y : R) : R :=
  Φ.eval₂ (evX x) y

theorem aeval_toRingHom_eq_evX {R : Type*} [CommRing R] [Algebra ℤ R] (x : R) :
    (Polynomial.aeval x).toRingHom = evX x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [evX])

theorem ringHom_comp_evX {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (x : R) : g.comp (evX x) = evX (g x) :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [evX])

theorem map_ev {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (x y : R) : g (ev Φ x y) = ev Φ (g x) (g y) := by
  unfold ev
  rw [Polynomial.hom_eval₂, ringHom_comp_evX]

theorem ev_eq_eval_map {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    ev Φ x y = (Φ.map (evX x)).eval y := by
  rw [ev, Polynomial.eval_map]

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffEmb_injective : Function.Injective (coeffEmb K) := by
  intro x y h
  ext k
  apply (algebraMap ℚ K).injective
  rw [← coeffEmb_coeff, ← coeffEmb_coeff, h]

theorem coeffEmb_qExpand (m : ℕ) [NeZero m] (f : LaurentSeries ℚ) :
    coeffEmb K (qExpand ℚ m f) = qExpand K m (coeffEmb K f) := by
  ext k
  by_cases hk : (m : ℤ) ∣ k
  · obtain ⟨i, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd m _ hk, qExpand_coeff_of_not_dvd m _ hk,
      map_zero]

abbrev J : LaurentSeries K := coeffEmb K jq

theorem coeff_slot_neg {m : ℕ} [NeZero m] (u : Kˣ) :
    (qExpand K m (qTwist u (J K))).coeff (-(m : ℤ)) ≠ 0 := by
  rw [show (-(m : ℤ)) = (m : ℤ) * (-1) by ring, qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff,
    coeff_jq_neg_one, map_one, mul_one]
  exact Units.ne_zero _

theorem coeff_slot_of_lt {m : ℕ} [NeZero m] (u : Kˣ) {k : ℤ} (hk : k < -(m : ℤ)) :
    (qExpand K m (qTwist u (J K))).coeff k = 0 := by
  by_cases hkm : (m : ℤ) ∣ k
  · obtain ⟨i, rfl⟩ := hkm
    have hi : i < -1 := by
      by_contra hi
      push Not at hi
      have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
      nlinarith
    rw [qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff, coeff_jq_of_lt hi, map_zero, mul_zero]
  · exact qExpand_coeff_of_not_dvd m _ hkm

theorem slot_index_eq {m m' : ℕ} [NeZero m] [NeZero m'] {u u' : Kˣ}
    (h : qExpand K m (qTwist u (J K)) = qExpand K m' (qTwist u' (J K))) : m = m' := by
  have h1 : ¬ (-(m : ℤ)) < -(m' : ℤ) := fun hlt =>
    coeff_slot_neg K u (by rw [h]; exact coeff_slot_of_lt K u' hlt)
  have h2 : ¬ (-(m' : ℤ)) < -(m : ℤ) := fun hlt =>
    coeff_slot_neg K u' (by rw [← h]; exact coeff_slot_of_lt K u hlt)
  omega

def dat (M : ℕ) [NeZero M] : ModularPolynomialData M :=
  Classical.choice (ModularCurve.nonempty_modularPolynomialData M)

theorem full_eq (M : ℕ) [NeZero M] : modularFunctionFieldFull M = modularFunctionField M :=
  (ModularCurve.functionFieldGeneration_iff_full_eq M).mp (ModularCurve.functionFieldGeneration M)

theorem hall (M : ℕ) : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
      ∧ modularFunctionField d = modularFunctionFieldFull d :=
  fun d _ _ => ⟨ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi d, (full_eq d).symm⟩

theorem phi_map_eq_prod_slots (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) :
    (dat M).Φ.map (evX (qExpand K M (J K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (X - C (if h : a = 0 then 0 else letI : NeZero a := ⟨h⟩;
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (J K)))) := by
  have h := ModularCurve.minpoly_jqN_map_eq_prod_slots (K := K) M ζ hζ (hall M)
  rw [ModularCurve.minpoly_jqN_eq_toAdjoin (dat M) (ModularCurve.phiIrreducible_all M (dat M)),
    ModularPolynomialData.toAdjoin, Polynomial.map_map] at h
  convert h using 2
  case e'_4 => rfl
  rw [RingHom.comp_assoc, algebraMap_comp_evalAtJGen, evalAtJ_def, aeval_toRingHom_eq_evX,
    ringHom_comp_evX, RingHom.comp_apply]
  erw [coeffEmb_qExpand]

theorem exists_slot_of_ev_eq_zero (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    {z : LaurentSeries K} (hz : ev (dat M).Φ (qExpand K M (J K)) z = 0) :
    ∃ a ∈ M.divisors, ∃ b ∈ (Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1), ∃ (_ : NeZero a),
      z = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (J K)) := by
  rw [ev_eq_eval_map, phi_map_eq_prod_slots K M ζ hζ, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨b, hb, hz⟩ := hz
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dif_neg ha0, eval_sub, eval_X, eval_C, sub_eq_zero] at hz
  exact ⟨a, ha, b, hb, ⟨ha0⟩, hz⟩

theorem exists_primitiveRoot_unit (M : ℕ) [NeZero M] :
    ∃ ζ : (CyclotomicField M ℚ)ˣ, IsPrimitiveRoot (ζ : CyclotomicField M ℚ) M := by
  haveI : NeZero ((M : ℕ) : ℚ) := NeZero.charZero
  have hζ := @IsCyclotomicExtension.zeta_spec M _ ℚ (CyclotomicField M ℚ) _ _ _
    (CyclotomicField.isCyclotomicExtension M ℚ)
  exact ⟨(hζ.isUnit (NeZero.ne M)).unit, by rw [IsUnit.unit_spec]; exact hζ⟩

theorem hswap (M : ℕ) [NeZero M] : (dat M).Φ.eval₂ (evalAtJqN M) jq = 0 := by

  obtain ⟨ζ, hζ'⟩ := exists_primitiveRoot_unit M
  apply coeffEmb_injective (CyclotomicField M ℚ)
  rw [map_zero, evalAtJqN_def, aeval_toRingHom_eq_evX]
  change coeffEmb (CyclotomicField M ℚ) (ev (dat M).Φ (jqN M) jq) = 0
  rw [map_ev, jqN, coeffEmb_qExpand, ev_eq_eval_map,
    phi_map_eq_prod_slots (CyclotomicField M ℚ) M ζ hζ', Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := 1) (by simp [NeZero.ne M]) ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := 0) ?_ ?_
  · simp [Nat.pos_of_ne_zero (NeZero.ne M)]
  · rw [dif_neg one_ne_zero, eval_sub, eval_X, eval_C, zero_mul, pow_zero, qTwist_one_apply,
      qExpand_congr (mul_one 1), qExpand_one_apply, sub_self]

end FrickeGeneral

scoped instance FrickeGeneral.instIsScalarTowerRat {L : Type*} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : IsScalarTower ℚ F L :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)

p2m_reactivate "P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero.FrickeGeneral"
namespace FrickeGeneral

section Engine

variable (N : ℕ) [NeZero N]

theorem modularFunctionField_eq_restrictScalars :
    modularFunctionField N = (ℚ⟮jq⟯⟮jqN N⟯).restrictScalars ℚ := by
  have h := IntermediateField.adjoin_adjoin_left (F := ℚ)
    (S := ({jq} : Set (LaurentSeries ℚ))) (T := {jqN N})
  rw [Set.singleton_union] at h
  exact h.symm

def relativeRingEquiv : (ℚ⟮jq⟯⟮jqN N⟯) ≃+* modularFunctionField N where
  toFun x := ⟨(x : LaurentSeries ℚ),
    (SetLike.ext_iff.mp (modularFunctionField_eq_restrictScalars N) _).mpr x.2⟩
  invFun y := ⟨(y : LaurentSeries ℚ),
    (SetLike.ext_iff.mp (modularFunctionField_eq_restrictScalars N) _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def frickeBaseHom : ℚ⟮jq⟯ →+* LaurentSeries ℚ :=
  (qExpand ℚ N).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))

theorem frickeBaseHom_comp_evalAtJGen : (frickeBaseHom N).comp evalAtJGen = evalAtJqN N := by
  rw [frickeBaseHom, RingHom.comp_assoc, algebraMap_comp_evalAtJGen, evalAtJ_def, evalAtJqN_def,
    aeval_toRingHom_eq_evX, aeval_toRingHom_eq_evX, ringHom_comp_evX]
  rfl

theorem isIntegral_jqN : IsIntegral ℚ⟮jq⟯ (jqN N) := by
  refine ⟨(dat N).toAdjoin, (dat N).toAdjoin_monic, ?_⟩
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact (dat N).eval_eq_zero

theorem eval₂_minpoly_frickeBaseHom :
    (minpoly ℚ⟮jq⟯ (jqN N)).eval₂ (frickeBaseHom N) jq = 0 := by
  rw [ModularCurve.minpoly_jqN_eq_toAdjoin (dat N) (ModularCurve.phiIrreducible_all N (dat N)),
    ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, frickeBaseHom_comp_evalAtJGen]
  exact hswap N

def frickeRelativeHom : ℚ⟮jq⟯⟮jqN N⟯ →+* LaurentSeries ℚ :=
  (AdjoinRoot.lift (frickeBaseHom N) jq (eval₂_minpoly_frickeBaseHom N)).comp
    (adjoinRootEquivAdjoin ℚ⟮jq⟯ (isIntegral_jqN N)).symm.toAlgHom.toRingHom

theorem frickeRelativeHom_gen :
    frickeRelativeHom N (AdjoinSimple.gen ℚ⟮jq⟯ (jqN N)) = jq := by
  rw [frickeRelativeHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin ℚ⟮jq⟯ (isIntegral_jqN N)).symm.toAlgHom.toRingHom
        (AdjoinSimple.gen ℚ⟮jq⟯ (jqN N))
      = AdjoinRoot.root (minpoly ℚ⟮jq⟯ (jqN N)) from
    adjoinRootEquivAdjoin_symm_apply_gen ℚ⟮jq⟯ (isIntegral_jqN N)]
  exact AdjoinRoot.lift_root _

theorem frickeRelativeHom_algebraMap (c : ℚ⟮jq⟯) :
    frickeRelativeHom N (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ c) = frickeBaseHom N c := by
  rw [frickeRelativeHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin ℚ⟮jq⟯ (isIntegral_jqN N)).symm.toAlgHom.toRingHom
        (algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ c)
      = algebraMap ℚ⟮jq⟯ (AdjoinRoot (minpoly ℚ⟮jq⟯ (jqN N))) c from
    (adjoinRootEquivAdjoin ℚ⟮jq⟯ (isIntegral_jqN N)).symm.commutes c]
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

def frickeAbsoluteHom : modularFunctionField N →+* LaurentSeries ℚ :=
  (frickeRelativeHom N).comp (relativeRingEquiv N).symm.toRingHom

theorem frickeAbsoluteHom_j : frickeAbsoluteHom N ⟨jq, jq_mem N⟩ = jqN N := by
  show frickeRelativeHom N ((relativeRingEquiv N).symm ⟨jq, jq_mem N⟩) = jqN N
  rw [show (relativeRingEquiv N).symm ⟨jq, jq_mem N⟩ = algebraMap ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN N⟯ jGen from
    Subtype.ext rfl]
  rw [frickeRelativeHom_algebraMap]
  rfl

theorem frickeAbsoluteHom_jN : frickeAbsoluteHom N ⟨jqN N, jqN_mem N⟩ = jq := by
  show frickeRelativeHom N ((relativeRingEquiv N).symm ⟨jqN N, jqN_mem N⟩) = jq
  rw [show (relativeRingEquiv N).symm ⟨jqN N, jqN_mem N⟩ = AdjoinSimple.gen ℚ⟮jq⟯ (jqN N) from
    Subtype.ext rfl]
  exact frickeRelativeHom_gen N

theorem mem_of_apply_gens_mem (f : modularFunctionField N →+* LaurentSeries ℚ)
    (E : IntermediateField ℚ (LaurentSeries ℚ))
    (hj : f ⟨jq, jq_mem N⟩ ∈ E) (hjN : f ⟨jqN N, jqN_mem N⟩ ∈ E) (x : modularFunctionField N) :
    f x ∈ E := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hyS =>
      rcases hyS with rfl | rfl
      · exact hj
      · exact hjN
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          (modularFunctionField N).algebraMap_mem r⟩ : modularFunctionField N)
          = (r : modularFunctionField N) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r
          = ((r : modularFunctionField N) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]
        norm_cast
      have hmem : f (r : modularFunctionField N) ∈ E := by
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem E r
      exact (congrArg f hr).symm ▸ hmem
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ E
      rw [map_add]
      exact add_mem ihx ihy
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) ∈ E
      rw [map_inv₀]
      exact inv_mem ih
  | mul x y hx hy ihx ihy =>
      have key : (⟨x * y, mul_mem hx hy⟩ : modularFunctionField N) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
        Subtype.ext ((modularFunctionField N).coe_mul ⟨x, hx⟩ ⟨y, hy⟩).symm
      have hmem : f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ E := by
        rw [map_mul]
        exact mul_mem ihx ihy
      exact (congrArg f key).symm ▸ hmem

theorem frickeAbsoluteHom_mem (x : modularFunctionField N) :
    frickeAbsoluteHom N x ∈ modularFunctionField N := by
  refine mem_of_apply_gens_mem N (frickeAbsoluteHom N) (modularFunctionField N) ?_ ?_ x
  · rw [frickeAbsoluteHom_j]; exact jqN_mem N
  · rw [frickeAbsoluteHom_jN]; exact jq_mem N

def frickeEndoRingHom : modularFunctionField N →+* modularFunctionField N :=
  (frickeAbsoluteHom N).codRestrict (modularFunctionField N) (frickeAbsoluteHom_mem N)

def frickeEndoAlgHom : modularFunctionField N →ₐ[ℚ] modularFunctionField N where
  toRingHom := frickeEndoRingHom N
  commutes' r := by
    rw [eq_ratCast (algebraMap ℚ (modularFunctionField N)) r]
    exact map_ratCast (frickeEndoRingHom N) r

theorem frickeEndoAlgHom_j : frickeEndoAlgHom N ⟨jq, jq_mem N⟩ = ⟨jqN N, jqN_mem N⟩ :=
  Subtype.ext (frickeAbsoluteHom_j N)

theorem frickeEndoAlgHom_jN : frickeEndoAlgHom N ⟨jqN N, jqN_mem N⟩ = ⟨jq, jq_mem N⟩ :=
  Subtype.ext (frickeAbsoluteHom_jN N)

theorem algHom_ext_of_eq_on_gens {A : Type*} [DivisionRing A] [Algebra ℚ A]
    {f g : modularFunctionField N →ₐ[ℚ] A}
    (hj : f ⟨jq, jq_mem N⟩ = g ⟨jq, jq_mem N⟩)
    (hjN : f ⟨jqN N, jqN_mem N⟩ = g ⟨jqN N, jqN_mem N⟩) : f = g := by
  ext ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hxS =>
      rcases hxS with rfl | rfl
      · exact hj
      · exact hjN
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          (modularFunctionField N).algebraMap_mem r⟩ : modularFunctionField N)
          = algebraMap ℚ (modularFunctionField N) r := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r
          = ((algebraMap ℚ (modularFunctionField N) r : modularFunctionField N) :
              LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r,
          eq_ratCast (algebraMap ℚ (modularFunctionField N)) r]
        norm_cast
      exact (congrArg f hr).trans
        ((f.commutes r).trans ((g.commutes r).symm.trans (congrArg g hr.symm)))
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

def frickeAlgEquiv : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N :=
  have hcomp : (frickeEndoAlgHom N).comp (frickeEndoAlgHom N)
      = AlgHom.id ℚ (modularFunctionField N) := by
    refine algHom_ext_of_eq_on_gens N ?_ ?_
    · show frickeEndoAlgHom N (frickeEndoAlgHom N ⟨jq, jq_mem N⟩) = ⟨jq, jq_mem N⟩
      rw [frickeEndoAlgHom_j, frickeEndoAlgHom_jN]
    · show frickeEndoAlgHom N (frickeEndoAlgHom N ⟨jqN N, jqN_mem N⟩) = ⟨jqN N, jqN_mem N⟩
      rw [frickeEndoAlgHom_jN, frickeEndoAlgHom_j]
  AlgEquiv.ofAlgHom (frickeEndoAlgHom N) (frickeEndoAlgHom N) hcomp hcomp

theorem coe_frickeAlgEquiv_apply (x : modularFunctionField N) :
    ((frickeAlgEquiv N x : modularFunctionField N) : LaurentSeries ℚ) = frickeAbsoluteHom N x :=
  rfl

theorem isFrickeAut_frickeAlgEquiv : IsFrickeAut N (frickeAlgEquiv N) :=
  ⟨frickeEndoAlgHom_j N, frickeEndoAlgHom_jN N⟩

end Engine
p2m_reactivate "P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero.FrickeGeneral"

section Slots

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem exists_slot_of_ev_map_eq_zero (M : ℕ) [NeZero M] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (φ : LaurentSeries K →+* LaurentSeries K)
    {z : LaurentSeries K} (hz : ev (dat M).Φ (φ (qExpand K M (J K))) z = 0) :
    ∃ a ∈ M.divisors, ∃ b ∈ (Finset.range (M / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1), ∃ (_ : NeZero a),
      z = φ (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (J K))) := by
  have h := congrArg (Polynomial.map φ) (phi_map_eq_prod_slots K M ζ hζ)
  rw [Polynomial.map_map, ringHom_comp_evX] at h
  rw [ev_eq_eval_map, h, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  rw [Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨b, hb, hz⟩ := hz
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dif_neg ha0, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X,
    eval_C, sub_eq_zero] at hz
  exact ⟨a, ha, b, hb, ⟨ha0⟩, hz⟩

end Slots
p2m_reactivate "P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero.FrickeGeneral"

section Swap

variable (N : ℕ) [NeZero N]

theorem apply_qExpand_eq (τ : modularFunctionField N →+* LaurentSeries ℚ)
    (hτj : τ ⟨jq, jq_mem N⟩ = jqN N) (hτjN : τ ⟨jqN N, jqN_mem N⟩ = jq)
    (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b]
    (hx : qExpand ℚ a jq ∈ modularFunctionField N) :
    τ ⟨qExpand ℚ a jq, hx⟩ = qExpand ℚ b jq := by
  set y := τ ⟨qExpand ℚ a jq, hx⟩ with hy

  have hF2 : ev (dat a).Φ (jqN N) y = 0 := by
    have h0 : ev (dat a).Φ (⟨jq, jq_mem N⟩ : modularFunctionField N) ⟨qExpand ℚ a jq, hx⟩ = 0 := by
      apply (algebraMap (modularFunctionField N) (LaurentSeries ℚ)).injective
      rw [map_ev, map_zero]
      have := (dat a).eval_eq_zero
      rw [evalAtJ_def, aeval_toRingHom_eq_evX] at this
      exact this
    have := congrArg τ h0
    rwa [map_ev, map_zero, hτj] at this

  have hF1 : ev (dat b).Φ jq y = 0 := by
    have hL : ev (dat b).Φ (jqN N) (qExpand ℚ a jq) = 0 := by
      have := congrArg (qExpand ℚ a) (show ev (dat b).Φ (jqN b) jq = 0 by
        have := hswap b
        rwa [evalAtJqN_def, aeval_toRingHom_eq_evX] at this)
      rwa [map_ev, map_zero, jqN, qExpand_qExpand, qExpand_congr hab] at this
    have h0 : ev (dat b).Φ (⟨jqN N, jqN_mem N⟩ : modularFunctionField N)
        ⟨qExpand ℚ a jq, hx⟩ = 0 := by
      apply (algebraMap (modularFunctionField N) (LaurentSeries ℚ)).injective
      rw [map_ev, map_zero]
      exact hL
    have := congrArg τ h0
    rwa [map_ev, map_zero, hτjN] at this

  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_unit N
  set K := CyclotomicField N ℚ
  set g : LaurentSeries ℚ →+* LaurentSeries K := coeffEmb K with hg
  have hζa : IsPrimitiveRoot ((ζ ^ b : Kˣ) : K) a := by
    rw [Units.val_pow_eq_pow_val]; exact hζ.pow (NeZero.pos N) (by rw [← hab, Nat.mul_comm])
  have hζb : IsPrimitiveRoot ((ζ ^ a : Kˣ) : K) b := by
    rw [Units.val_pow_eq_pow_val]; exact hζ.pow (NeZero.pos N) hab.symm

  have h1 : ev (dat b).Φ (qExpand K b (J K)) (qExpand K b (g y)) = 0 := by
    have := congrArg (qExpand K b) (congrArg g hF1)
    rwa [map_ev, map_zero, map_ev, map_zero] at this
  obtain ⟨α, hα, β, hβ, _, h1⟩ := exists_slot_of_ev_eq_zero K b (ζ ^ a) hζb h1

  have h2 : ev (dat a).Φ (qExpand K b (qExpand K a (J K))) (g y) = 0 := by
    have := congrArg g hF2
    rwa [map_ev, map_zero, jqN, hg, coeffEmb_qExpand, ← qExpand_congr (Nat.mul_comm a b ▸ hab),
      ← qExpand_qExpand] at this
  obtain ⟨α', hα', β', hβ', _, h2⟩ :=
    exists_slot_of_ev_map_eq_zero K a (ζ ^ b) hζa (qExpand K b) h2

  have h2' := congrArg (qExpand K b) h2
  rw [qExpand_qExpand, qExpand_qExpand] at h2'
  have hidx : α * α = b * b * (α' * α') := slot_index_eq K (h1.symm.trans h2')
  have hαb : α = b := by
    have hle : α ≤ b := Nat.le_of_dvd (NeZero.pos b) (Nat.mem_divisors.mp hα).1
    have h1le : 1 ≤ α' * α' := NeZero.one_le
    have hge : b * b ≤ α * α := by
      rw [hidx]
      exact Nat.le_mul_of_pos_right _ h1le
    exact le_antisymm hle (Nat.mul_self_le_mul_self_iff.mp hge)
  subst hαb
  have hβ0 : β = 0 := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hβ).1
    rw [Nat.div_self (NeZero.pos α)] at this
    omega
  rw [hβ0, zero_mul, pow_zero, qTwist_one_apply, ← qExpand_qExpand] at h1
  have h3 : g y = g (qExpand ℚ α jq) := by
    rw [hg, coeffEmb_qExpand]; exact qExpand_injective α h1
  exact coeffEmb_injective K h3

def fullRingEquiv : modularFunctionFieldFull N ≃+* modularFunctionField N where
  toFun x := ⟨(x : LaurentSeries ℚ), (SetLike.ext_iff.mp (full_eq N) _).mp x.2⟩
  invFun y := ⟨(y : LaurentSeries ℚ), (SetLike.ext_iff.mp (full_eq N) _).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def frickeRingEquivFull : modularFunctionFieldFull N ≃+* modularFunctionFieldFull N :=
  ((fullRingEquiv N).trans (frickeAlgEquiv N).toRingEquiv).trans (fullRingEquiv N).symm

def frickeAlgEquivFull : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N :=
  { frickeRingEquivFull N with
    commutes' := fun r => by
      show frickeRingEquivFull N (algebraMap ℚ (modularFunctionFieldFull N) r)
        = algebraMap ℚ (modularFunctionFieldFull N) r
      rw [eq_ratCast (algebraMap ℚ (modularFunctionFieldFull N)) r]
      exact map_ratCast (frickeRingEquivFull N).toRingHom r }

theorem coe_frickeAlgEquivFull_apply (x : modularFunctionFieldFull N) :
    ((frickeAlgEquivFull N x : modularFunctionFieldFull N) : LaurentSeries ℚ)
      = frickeAbsoluteHom N ⟨x, (SetLike.ext_iff.mp (full_eq N) _).mp x.2⟩ :=
  rfl

theorem isFrickeAutFull_frickeAlgEquivFull : IsFrickeAutFull N (frickeAlgEquivFull N) := by
  intro a b hab _ _
  apply Subtype.ext
  rw [coe_frickeAlgEquivFull_apply]
  exact apply_qExpand_eq N (frickeAbsoluteHom N) (frickeAbsoluteHom_j N) (frickeAbsoluteHom_jN N)
    a b hab _

end Swap
p2m_reactivate "P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero.FrickeGeneral"

end FrickeGeneral
p2m_reactivate "P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero.FrickeGeneral"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero.FrickeGeneral"

theorem solution (N : ℕ) [NeZero N] :
    ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ :=
  ⟨FrickeGeneral.frickeAlgEquivFull N, FrickeGeneral.isFrickeAutFull_frickeAlgEquivFull N⟩

end S_ModularCurve_exists_isFrickeAutFull_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_isFrickeAutFull_of_neZero (solution)
