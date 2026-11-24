-- Prove2me | solution 1 for GlobalTheory.SecAff.sec_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:37.405501+00:00
-- url     : https://prove2.me/submissions/9ebc8521-f331-4379-929a-abe0498577a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_rs_rs
import Theorems.Thm_GlobalTheory_SecAff_eq_of_cover
import Theorems.Thm_GlobalTheory_SecAff_glue_cover
import Theorems.Thm_GlobalTheory_SecAff_fun_extend
import Theorems.Thm_GlobalTheory_SecAff_fun_kill
import Theorems.Thm_GlobalTheory_SecAff_pow_mul_zero_mono
import Theorems.Thm_GlobalTheory_SecAff_exists_fin_cover
import Theorems.Thm_GlobalTheory_SecAff_cocycle_at
import Theorems.Thm_GlobalTheory_SecAff_le_iSup_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution [CompactSpace X] [QuasiSeparatedSpace X] (φ : X' ⟶ X) [IsOpenImmersion φ]
    (f : Γ(X, ⊤)) (hφ : φ.opensRange = X.basicOpen f) (M : LB X) (hM : M.IsLB)
    (U' : M.ι → X'.Opens) (h : ∀ j, U' j ≤ φ ⁻¹ᵁ M.U j) (h' : ∀ j, φ ⁻¹ᵁ M.U j ≤ U' j)
    (t : ∀ j, Γ(X', U' j))
    (ht : ∀ i j, rs (inf_le_left : U' i ⊓ U' j ≤ U' i) (t i) =
      pa φ (le_pre_inf (inf_le_left.trans (h i)) (inf_le_right.trans (h j)))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : U' i ⊓ U' j ≤ U' j) (t j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ j, pa φ (h j) (s.f j) = pa φ (le_pre_top φ) f ^ N * t j := by
  obtain ⟨κ, _, W, c, hW, hWc, hc⟩ := exists_fin_cover M hM
  have hWU : ∀ a, φ ⁻¹ᵁ W a ≤ U' (c a) := fun a => (φ.preimage_mono (hWc a)).trans (h' (c a))
  have ht' : ∀ i j {V : X'.Opens} (hi : V ≤ U' i) (hj : V ≤ U' j), rs hi (t i) =
      pa φ (le_pre_inf (hi.trans (h i)) (hj.trans (h j)))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs hj (t j) := by
    intro i j V hi hj
    have := congrArg (rs (le_inf hi hj)) (ht i j)
    rwa [map_mul, rs_rs, rs_rs, rs_pa] at this
  choose n x hx using fun a => fun_extend φ f hφ (hW a) le_rfl le_rfl (rs (hWU a) (t (c a)))
  obtain ⟨N, hN⟩ : ∃ N, ∀ a, n a ≤ N := ⟨Finset.univ.sup n, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  let x' : ∀ a, Γ(X, W a) := fun a => rs le_top f ^ (N - n a) * x a
  have hx' : ∀ a {V : X'.Opens} (hV : V ≤ φ ⁻¹ᵁ W a), pa φ hV (x' a) =
      pa φ (le_pre_top φ) f ^ N * rs (hV.trans (hWU a)) (t (c a)) := by
    intro a V hV
    have := congrArg (rs hV) (hx a)
    rw [rs_pa, map_mul, map_pow, rs_pa, rs_rs] at this
    simp only [x']
    rw [map_mul, map_pow, pa_rs, this, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (hN a)]
  clear_value x'
  have hk : ∀ p : κ × κ, ∃ K : ℕ, rs (le_top : W p.1 ⊓ W p.2 ≤ ⊤) f ^ K *
      (rs inf_le_left (x' p.1) - rs (inf_le_inf (hWc p.1) (hWc p.2))
        (M.g (c p.1) (c p.2) : Γ(X, M.U (c p.1) ⊓ M.U (c p.2))) * rs inf_le_right (x' p.2)) = 0 := by
    rintro ⟨a, b⟩
    refine fun_kill φ f hφ (QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hW a).isCompact
      (W b).isOpen (hW b).isCompact) le_rfl le_rfl _ ?_
    rw [map_sub, map_mul, pa_rs, pa_rs, pa_rs, hx', hx', ht' (c a) (c b) _
      ((φ.preimage_mono inf_le_right).trans (hWU b))]
    ring
  choose k hk using hk
  obtain ⟨K, hK⟩ : ∃ K, ∀ p, k p ≤ K := ⟨Finset.univ.sup k, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  let y : ∀ a, Γ(X, W a) := fun a => rs le_top f ^ K * x' a
  have hy : ∀ a b {V : X.Opens} (ha : V ≤ W a) (hb : V ≤ W b), rs ha (y a) =
      rs (le_inf (ha.trans (hWc a)) (hb.trans (hWc b)))
        (M.g (c a) (c b) : Γ(X, M.U (c a) ⊓ M.U (c b))) * rs hb (y b) := by
    intro a b V ha hb
    have := congrArg (rs (le_inf ha hb)) (pow_mul_zero_mono (hk (a, b)) (hK (a, b)))
    simp only [map_mul, map_pow, map_sub, rs_rs, map_zero] at this
    simp only [y, map_mul, map_pow, rs_rs]
    linear_combination this
  have hg : ∀ j, ∃ z : Γ(X, M.U j), ∀ a, rs (inf_le_left : M.U j ⊓ W a ≤ M.U j) z =
      rs (inf_le_inf le_rfl (hWc a)) (M.g j (c a) : Γ(X, M.U j ⊓ M.U (c a))) *
        rs inf_le_right (y a) := by
    intro j
    refine glue_cover (fun a => M.U j ⊓ W a) (fun a => inf_le_left) (le_iSup_inf _ hc) _
      fun a b => ?_
    simp only [map_mul, rs_rs]
    rw [hy a b _ (inf_le_right.trans inf_le_right), ← _root_.mul_assoc, cocycle_at hM]
  choose z hz using hg
  have hz' : ∀ j a {V : X.Opens} (hj : V ≤ M.U j) (ha : V ≤ W a), rs hj (z j) =
      rs (le_inf hj (ha.trans (hWc a))) (M.g j (c a) : Γ(X, M.U j ⊓ M.U (c a))) * rs ha (y a) := by
    intro j a V hj ha
    have := congrArg (rs (le_inf hj ha)) (hz j a)
    rwa [map_mul, rs_rs, rs_rs, rs_rs] at this
  refine ⟨K + N, ⟨z, fun i j => ?_⟩, fun j => ?_⟩
  · change rs inf_le_left (z i) = (M.g i j : Γ(X, M.U i ⊓ M.U j)) * rs inf_le_right (z j)
    refine eq_of_cover (fun a => M.U i ⊓ M.U j ⊓ W a) (fun a => inf_le_left) (le_iSup_inf _ hc)
      _ _ fun a => ?_
    rw [map_mul, rs_rs, rs_rs, hz' i a _ inf_le_right, hz' j a _ inf_le_right, ← _root_.mul_assoc,
      cocycle_at hM]
  · refine eq_of_cover (fun a => U' j ⊓ φ ⁻¹ᵁ W a) (fun a => inf_le_left)
      (le_iSup_inf _ ?_) _ _ fun a => ?_
    · intro q _
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
        (hc (TopologicalSpace.Opens.mem_top (φ q)))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
    have hV : U' j ⊓ φ ⁻¹ᵁ W a ≤ φ ⁻¹ᵁ (M.U j ⊓ W a) :=
      le_pre_inf (inf_le_left.trans (h j)) inf_le_right
    have := congrArg (pa φ hV) (hz j a)
    rw [pa_rs, map_mul, pa_rs, pa_rs] at this
    simp only [y] at this
    rw [map_mul, map_pow, pa_rs, hx'] at this
    rw [rs_pa, this, map_mul, map_pow, rs_pa, ht' j (c a) _ (inf_le_right.trans (hWU a))]
    ring
end GlobalTheory.SecAff
