-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.exists_eq_span_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:34:10.620574+00:00
-- url     : https://prove2.me/submissions/4ff84ad1-4054-4eeb-a258-410e02bcd041

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (n : ℕ) :
    ∀ N : Submodule R (Fin n → R), ∃ b : Fin n → Fin n → R,
      N = Submodule.span R (Set.range b) := by
  induction n with
  | zero => intro N; exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro N
    let ι : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
      { toFun := fun v => Fin.cons 0 v
        map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
        map_smul' := fun c v => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
    obtain ⟨b, hb⟩ := ih (N.comap ι)
    obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal
      (N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0))
    obtain ⟨x, hx, hxg⟩ : g ∈ N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0) :=
      hg ▸ Submodule.mem_span_singleton_self g
    refine ⟨Fin.cons x fun i => ι (b i), le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hg ▸ Submodule.mem_map_of_mem hy)
      have h0 : (y - a • x) 0 = 0 := by
        have h1 : x 0 = g := hxg
        have h2 : a * g = y 0 := ha
        simp [h1, h2]
      have h1 : ι (Fin.tail (y - a • x)) = y - a • x := by
        show Fin.cons 0 (Fin.tail (y - a • x)) = _
        rw [← h0, Fin.cons_self_tail]
      have h2 : Fin.tail (y - a • x) ∈ N.comap ι := by
        rw [Submodule.mem_comap, h1]; exact N.sub_mem hy (N.smul_mem a hx)
      rw [hb] at h2
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨Fin.cons a d, ?_⟩
      rw [← hd, map_sum] at h1
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← map_smul, h1]
      abel
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases hx (fun i => ?_) i
      have : b i ∈ N.comap ι := hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this
end GlobalTheory.HL.SelfDual
