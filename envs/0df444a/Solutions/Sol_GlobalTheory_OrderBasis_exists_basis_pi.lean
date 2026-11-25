-- Prove2me | solution 1 for GlobalTheory.OrderBasis.exists_basis_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:52.012798+00:00
-- url     : https://prove2.me/submissions/73411cbb-4271-4e5f-92ca-01e51a516ce5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrderBasis
namespace GlobalTheory.OrderBasis
theorem _root_.solution {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (s t : E) (hs : IsUnit s) (ht : IsUnit t) :
    ∀ (m : ℕ) (Q : Submodule R (Fin m → E)), (∀ q ∈ Q, ∀ i, s * q i ∈ R) →
      (∀ i, (Pi.single i t : Fin m → E) ∈ Q) →
      ∃ b : Fin m → Fin m → E, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  intro m
  induction m with
  | zero =>
    intro Q _ _
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, Subsingleton.elim _ _⟩
  | succ m ih =>
    intro Q h1 h2
    let I : Ideal R :=
      { carrier := {r | ∃ q ∈ Q, s * q 0 = r}
        add_mem' := by
          rintro a b ⟨p, hp, hpa⟩ ⟨q, hq, hqb⟩
          exact ⟨p + q, Q.add_mem hp hq, by simp [mul_add, hpa, hqb]⟩
        zero_mem' := ⟨0, Q.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨p, hp, hpa⟩
          refine ⟨c • p, Q.smul_mem c hp, ?_⟩
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Subring.coe_mul, ← hpa]
          ring }
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
    obtain ⟨q0, hq0, hq0a⟩ := haI
    have hmul : ∀ q ∈ Q, ∃ c : R, q 0 = c * q0 0 := by
      intro q hq
      have : (⟨s * q 0, h1 q hq 0⟩ : R) ∈ I := ⟨q, hq, rfl⟩
      rw [ha, Submodule.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨c, hs.mul_left_cancel ?_⟩
      have := congrArg Subtype.val hc
      simp only [smul_eq_mul, Subring.coe_mul] at this
      rw [← this, ← hq0a]; ring
    have hu : IsUnit (q0 0) := by
      obtain ⟨c, hc⟩ := hmul _ (h2 0)
      simp only [Pi.single_eq_same] at hc
      rw [hc] at ht
      exact isUnit_of_mul_isUnit_right ht
    let j : (Fin m → E) →ₗ[E] (Fin (m + 1) → E) :=
      LinearMap.pi (fun i => Fin.cases 0 (fun k => LinearMap.proj k) i)
    have j0 : ∀ v, j v 0 = 0 := fun v => by simp [j]
    have js : ∀ v k, j v (Fin.succ k) = v k := fun v k => by simp [j]
    obtain ⟨b, hb, hQ⟩ := ih (Q.comap (j.restrictScalars R))
      (fun q hq i => by have := h1 _ hq i.succ; simpa [js] using this)
      (fun i => by
        have : j (Pi.single i t) = Pi.single i.succ t := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
          · rw [js]; simp [Pi.single_apply]
        show j (Pi.single i t) ∈ Q
        rw [this]; exact h2 _)
    refine ⟨Fin.cons q0 (fun i => j (b i)), ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hg0 : g 0 = 0 := by
        have := congrFun hg 0
        simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, j0, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
        exact hu.mul_left_eq_zero.mp this
      have hgs : ∑ i, g (Fin.succ i) • b i = 0 := by
        funext k
        have := congrFun hg k.succ
        simpa [hg0, js, Finset.sum_apply] using this
      intro i
      refine Fin.cases hg0 (fun i => ?_) i
      exact Fintype.linearIndependent_iff.mp hb _ hgs i
    · apply le_antisymm
      · intro q hq
        obtain ⟨c, hc⟩ := hmul q hq
        have hq' : q - c • q0 ∈ Q := Q.sub_mem hq (Q.smul_mem c hq0)
        have he : j (fun k => (q - c • q0) k.succ) = q - c • q0 := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0]; simp [Subring.smul_def, hc]
          · rw [js]
        have hm : (fun k : Fin m => (q - c • q0) k.succ) ∈ Q.comap (j.restrictScalars R) := by
          show j _ ∈ Q
          rw [he]; exact hq'
        rw [hQ] at hm
        have hm2 := Submodule.mem_map_of_mem (f := j.restrictScalars R) hm
        rw [Submodule.map_span] at hm2
        have hm3 : q - c • q0 ∈ Submodule.span R
            (Set.range (Fin.cons q0 (fun i => j (b i)) : Fin (m + 1) → Fin (m + 1) → E)) := by
          rw [← he]
          refine Submodule.span_mono ?_ hm2
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i.succ, by simp⟩
        have : q = (q - c • q0) + c • q0 := by abel
        rw [this]
        exact Submodule.add_mem _ hm3 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases hq0 (fun i => ?_) i
        have : b i ∈ Q.comap (j.restrictScalars R) := by
          rw [hQ]; exact Submodule.subset_span ⟨i, rfl⟩
        simpa using this
end GlobalTheory.OrderBasis
