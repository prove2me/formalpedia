-- Prove2me | solution 1 for ModularCurve.slot_ord_of_algHom_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/73f0101f-89f1-523f-81b7-92a1087bfc65

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_order_qExpand
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_slot_ord_of_algHom_laurentBaseChange
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve AlgebraicCurve

namespace CD

section Helper

variable {K : Type*} [Field K]

theorem order_qTwist (u : Kˣ) (f : LaurentSeries K) : (qTwist u f).order = f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero]
  · have hne : qTwist u f ≠ 0 := fun h =>
      hf (qTwist_injective u (by rw [h, map_zero]))
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_)
      (HahnSeries.order_le_of_coeff_ne_zero ?_)
    · rw [qTwist_coeff]
      exact mul_ne_zero (Units.ne_zero _) (HahnSeries.coeff_order_eq_zero.not.mpr hf)
    · have := HahnSeries.coeff_order_eq_zero.not.mpr hne
      rw [qTwist_coeff] at this
      exact right_ne_zero_of_mul this

noncomputable def qExpandAlgK (M : ℕ) [NeZero M] : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K M
  commutes' r := by
    show qExpand K M (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

@[scoped simp]
theorem qExpandAlgK_apply (M : ℕ) [NeZero M] (f : LaurentSeries K) :
    qExpandAlgK M f = qExpand K M f := rfl

theorem qExpand_mem_range_of_dvd (M P : ℕ) [NeZero M] [NeZero P] (h : M ∣ P)
    (f : LaurentSeries K) :
    qExpand K P f ∈ (qExpandAlgK (K := K) M).fieldRange := by
  haveI : NeZero (P / M) :=
    ⟨Nat.div_ne_zero_iff.mpr ⟨NeZero.ne M, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne P)) h⟩⟩
  refine ⟨qExpand K (P / M) f, ?_⟩
  show qExpand K M (qExpand K (P / M) f) = qExpand K P f
  rw [qExpand_qExpand]
  exact qExpand_congr (Nat.mul_div_cancel' h) f

end Helper

variable (K : Type*) [Field K] [Algebra ℚ K]

private theorem _root_.ModularCurve.slot_ord_of_algHom_laurentBaseChange (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∣ N) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (w : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ : ℤ) (hγ : 0 < γ)
    (hw : ∀ x, w.ord x * γ = (ι x).order) :
    γ = a * Nat.gcd a (N / a) ∧
    w.ord ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        -((N / a / Nat.gcd a (N / a) : ℕ) : ℤ) ∧
    w.ord ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        -((a / Nat.gcd a (N / a) : ℕ) : ℤ) := by

  let F := laurentBaseChange K (modularFunctionFieldFull N)
  let jbar : F := ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩
  let jbarN : F :=
    ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩
  let g := Nat.gcd a (N / a)

  have ha0 : a ≠ 0 := NeZero.ne a
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left ha0
  haveI hag0 : NeZero (a * g) := ⟨Nat.mul_ne_zero ha0 hg0⟩
  have hag_dvd_N : a * g ∣ N := by
    calc a * g ∣ a * (N / a) := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_right _ _)
      _ = N := Nat.mul_div_cancel' ha
  have hag_dvd_aa : a * g ∣ a * a := Nat.mul_dvd_mul_left a (Nat.gcd_dvd_left _ _)
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero ha0 ha0⟩

  have hord1 : (ι jbar).order = -(N : ℤ) := by
    rw [show ι jbar = qExpand K N (coeffEmb K jq) from hι₁, order_qExpand, order_coeffEmb_jq,
      mul_neg_one]
  have hord2 : (ι jbarN).order = -((a * a : ℕ) : ℤ) := by
    rw [show ι jbarN = _ from hι₂, order_qExpand, order_qTwist, order_coeffEmb_jq,
      mul_neg_one]
  have hw1 : w.ord jbar * γ = -(N : ℤ) := (hw jbar).trans hord1
  have hw2 : w.ord jbarN * γ = -((a * a : ℕ) : ℤ) := (hw jbarN).trans hord2

  have hγdvd : γ ∣ ((a * g : ℕ) : ℤ) := by
    have hN : γ ∣ (N : ℤ) := ⟨-(w.ord jbar), by rw [mul_neg, mul_comm γ, hw1, neg_neg]⟩
    have haa : γ ∣ ((a * a : ℕ) : ℤ) :=
      ⟨-(w.ord jbarN), by rw [mul_neg, mul_comm γ, hw2, neg_neg]⟩
    have key : Nat.gcd N (a * a) = a * g := by
      conv_lhs => rw [← Nat.mul_div_cancel' ha]
      rw [Nat.gcd_mul_left, Nat.gcd_comm]
    rw [← key, Nat.gcd_eq_gcd_ab]
    exact dvd_add (Dvd.dvd.mul_right hN _) (Dvd.dvd.mul_right haa _)

  have hrange : ∀ x : F, ι x ∈ (qExpandAlgK (K := K) (a * g)).fieldRange := by

    have hadj := laurentBaseChange_adjoin_pair K N (functionFieldGeneration N)

    have htop : IntermediateField.adjoin K ({jbar, jbarN} : Set F) = ⊤ := by
      apply IntermediateField.map_injective F.val
      calc (IntermediateField.adjoin K ({jbar, jbarN} : Set F)).map F.val
          = IntermediateField.adjoin K (F.val '' {jbar, jbarN}) :=
            IntermediateField.adjoin_map K _ F.val
        _ = IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) := by
            congr 1
            rw [Set.image_insert_eq, Set.image_singleton]
            show ({coeffEmb K jq, coeffEmb K (jqN N)} : Set (LaurentSeries K)) = _
            rw [coeffEmb_jq K, coeffEmb_jqN K N]
        _ = F := hadj.symm
        _ = (⊤ : IntermediateField K F).map F.val :=
            (IntermediateField.fieldRange_val (S := F)).symm.trans
              (AlgHom.fieldRange_eq_map F.val)
    intro x
    have hxmem : x ∈ IntermediateField.adjoin K ({jbar, jbarN} : Set F) :=
      htop ▸ IntermediateField.mem_top

    induction hxmem using IntermediateField.adjoin_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hι₁ ▸ qExpand_mem_range_of_dvd (a * g) N hag_dvd_N (coeffEmb K jq)
      · exact hι₂ ▸ qExpand_mem_range_of_dvd (a * g) (a * a) hag_dvd_aa
          (qTwist (ζ ^ (b * a)) (coeffEmb K jq))
    | algebraMap c =>
      rw [AlgHom.commutes]
      exact IntermediateField.algebraMap_mem _ c
    | add y z _ _ ihy ihz => rw [map_add]; exact add_mem ihy ihz
    | inv y _ ih => rw [map_inv₀]; exact inv_mem ih
    | mul y z _ _ ihy ihz => rw [map_mul]; exact mul_mem ihy ihz

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨f, hfπ⟩ := hrange (π : F)
  have hγeq : γ = (ι (π : F)).order := by
    have := hw (π : F)
    rw [w.ord_coe_irreducible hπ, one_mul] at this
    exact this
  have hagdvdγ : ((a * g : ℕ) : ℤ) ∣ γ := by
    rw [hγeq, ← hfπ]
    show ((a * g : ℕ) : ℤ) ∣ (qExpandAlgK (a * g) f).order
    rw [qExpandAlgK_apply, order_qExpand]
    exact Dvd.intro _ rfl

  have hagpos : 0 < ((a * g : ℕ) : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero hag0.out
  have hγval : γ = ((a * g : ℕ) : ℤ) :=
    Int.dvd_antisymm (le_of_lt hγ) (le_of_lt hagpos) hγdvd hagdvdγ
  refine ⟨by rw [hγval]; push_cast; ring, ?_, ?_⟩
  ·
    have hdiv : (N / a / g) * (a * g) = N := by
      rw [Nat.div_div_eq_div_mul, Nat.div_mul_cancel hag_dvd_N]
    have key : (-((N / a / g : ℕ) : ℤ)) * ((a * g : ℕ) : ℤ) = -(N : ℤ) := by
      rw [neg_mul, ← Nat.cast_mul, hdiv]
    exact mul_right_cancel₀ (ne_of_gt hagpos) ((hγval ▸ hw1).trans key.symm)
  ·
    have hdiv : (a / g) * (a * g) = a * a := by
      rw [mul_comm a g, ← mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left a (N / a))]
    have key : (-((a / g : ℕ) : ℤ)) * ((a * g : ℕ) : ℤ) = -((a * a : ℕ) : ℤ) := by
      rw [neg_mul, ← Nat.cast_mul, hdiv]
    exact mul_right_cancel₀ (ne_of_gt hagpos) ((hγval ▸ hw2).trans key.symm)

p2m_alias "P2MW.S_ModularCurve_slot_ord_of_algHom_laurentBaseChange.ModularCurve.slot_ord_of_algHom_laurentBaseChange" "ModularCurve.slot_ord_of_algHom_laurentBaseChange"
end CD
p2m_reactivate "P2MW.S_ModularCurve_slot_ord_of_algHom_laurentBaseChange.CD"

open ModularCurve AlgebraicCurve in

theorem solution (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∣ N) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (w : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ : ℤ) (hγ : 0 < γ)
    (hw : ∀ x, w.ord x * γ = (ι x).order) :
    γ = a * Nat.gcd a (N / a) ∧
    w.ord ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        -((N / a / Nat.gcd a (N / a) : ℕ) : ℤ) ∧
    w.ord ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        -((a / Nat.gcd a (N / a) : ℕ) : ℤ) :=
  ModularCurve.slot_ord_of_algHom_laurentBaseChange K N ζ a b ha ι hι₁ hι₂ w γ hγ hw

#print axioms solution

end S_ModularCurve_slot_ord_of_algHom_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_slot_ord_of_algHom_laurentBaseChange (solution)
