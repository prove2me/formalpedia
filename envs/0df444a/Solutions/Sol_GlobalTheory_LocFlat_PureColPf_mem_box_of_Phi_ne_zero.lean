-- Prove2me | solution 1 for GlobalTheory.LocFlat.PureColPf.mem_box_of_Phi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:49.451817+00:00
-- url     : https://prove2.me/submissions/56d5a1e3-900e-4482-b981-088cd1e6b2cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_coords_entry
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_le_of_mul_pow_lt
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LocFlat.PureColPf
theorem _root_.solution (hpat : S.Pattern t) (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (hr : c + 1 = 2 * r)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hz : ∀ a, z (.inl a) (.inr ⟨r, by omega⟩) = 0) (y : XIx (Fin κ) t (j + 1) → k)
    (h : (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) ≠ 0) :
    y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹ := by
  have hρ : r ≤ S.ρ := by have := S.odd; omega
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  rw [hΦ] at h
  obtain ⟨⟨g, hg, e⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
  have hpg := ((hpat j g).1 hg).2
  set x := z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y with hx
  let q₀ : Fin (c + 1 + 1) := ⟨r, by omega⟩
  let b : Ix (Fin κ ⊕ Fin (s + 1)) t j := .inl (.inr ⟨r, by omega⟩)
  have hb : o' b = .inr q₀ := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (by omega) q₀
  intro a
  apply le_of_mul_pow_lt S.unif r
  have key : (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (o.symm (.inl a)) b = y a * (S.ϖ : k) ^ (r + 1) := by
    change (((typeFrame S.ϖ o).bas⁻¹).val * x * (typeFrame S.ϖ o').bas.val) (o (o.symm (.inl a))) (o' b) = _
    rw [Equiv.apply_symm_apply, hb, coords_entry]
    simp [hx, hz, q₀, colAt]
  rw [← key]
  obtain ⟨w, hw⟩ : ∃ w, ixSucc _ t j w = o.symm (.inl a) := ⟨_, Equiv.apply_symm_apply _ _⟩
  have hw' : o (ixSucc _ t j w) = .inl a := by rw [hw, Equiv.apply_symm_apply]
  rw [← hw]
  rcases w with i | u
  · have hgi : g.val i b = (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (ixSucc _ t j (.inl i)) b := by
      rw [e]; rfl
    have hnf : ¬ FreeIx S.ρ i b ∧ i ≠ b := by
      rcases i with (e' | l) | ⟨q, u⟩
      · refine ⟨?_, by simp [b]⟩
        simp only [FreeIx, FreeTop, b, Fin.mk_lt_mk, not_lt]
        exact hρ
      · have hl : c + 1 ≤ l.val := by
          by_contra hl
          push_neg at hl
          have h1 : o (.inl (.inr l)) = .inr ⟨l.val, hl⟩ :=
            standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) (c + 1) (by omega) (⟨l.val, hl⟩ : Fin (c + 1))
          have h2 : o (ixSucc _ t j (.inl (.inl (.inr l)))) = o (.inl (.inr l)) := rfl
          rw [h2, h1] at hw'
          exact Sum.inr_ne_inl hw'
        refine ⟨?_, ?_⟩
        · simp only [FreeIx, FreeTop, b, Fin.lt_def, not_lt]
          omega
        · intro he
          simp only [b, Sum.inl.injEq, Sum.inr.injEq] at he
          have := congrArg Fin.val he
          simp at this
          omega
      · exact ⟨by simp [FreeIx, b], by simp [b]⟩
    have := hpg i b hnf.1
    rw [Matrix.one_apply_ne hnf.2, sub_zero, hgi] at this
    exact this
  · exact hmax u b
end GlobalTheory.LocFlat.PureColPf
