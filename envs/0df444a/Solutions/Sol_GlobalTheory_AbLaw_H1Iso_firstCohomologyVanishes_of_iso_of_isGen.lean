-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.firstCohomologyVanishes_of_iso_of_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:17.653771+00:00
-- url     : https://prove2.me/submissions/3bd60de5-b297-422b-821d-2848c3e0e70b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_iso_rel
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_rs_g_self
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_rs_inv_mul

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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.H1Iso
theorem _root_.solution {N M : LB X} (hN : ⨆ i, N.U i = ⊤) (hM : M.IsLB) (w : LB.Iso M N)
    (hw : w.IsGen) (h0 : FirstCohomologyVanishes N) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  have hcov : ∀ W : X.Opens, W ≤ ⨆ i, W ⊓ N.U i := fun W x hx => by
    have hx' : x ∈ ⨆ i, N.U i := by rw [hN]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
  have hc' : ⨆ p : I × N.ι, V p.1 ⊓ N.U p.2 = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ ⨆ a, V a := by rw [hc]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov _ ha)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, i), hi⟩
  have hφ0 : ∀ a, φ a a = 0 := fun a => by
    have h := congrArg (rs X (le_inf le_rfl inf_le_left : V a ⊓ V a ≤ V a ⊓ V a ⊓ V a)) (hφ a a a)
    simp only [map_add, map_mul, rs_rs, rs_self, rs_g_self hM, _root_.one_mul] at h
    exact add_eq_left.1 h
  obtain ⟨ψ, hψ⟩ := h0 (I × N.ι) (fun p => V p.1 ⊓ N.U p.2) (fun p => p.2) (fun _ => inf_le_right) hc'
    (fun p q => rs X (le_inf (inf_le_left.trans inf_le_right) ((inf_le_left.trans inf_le_left).trans (hV p.1)) :
        V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ≤ N.U p.2 ⊓ M.U (c p.1)) (wu w p.2 (c p.1)).val *
      rs X (inf_le_inf inf_le_left inf_le_left : V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ≤ V p.1 ⊓ V q.1)
        (φ p.1 q.1))
    (fun p q r => by
      have h := congrArg (rs X (inf_le_inf (inf_le_inf inf_le_left inf_le_left) inf_le_left :
        V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ⊓ (V r.1 ⊓ N.U r.2) ≤ V p.1 ⊓ V q.1 ⊓ V r.1))
        (hφ p.1 q.1 r.1)
      have h' := iso_rel w hw p.2 q.2 (c p.1) (c q.1)
        (W := V p.1 ⊓ N.U p.2 ⊓ (V q.1 ⊓ N.U q.2) ⊓ (V r.1 ⊓ N.U r.2))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))
        (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (hV _))))
        (inf_le_left.trans (inf_le_right.trans (inf_le_left.trans (hV _))))
      simp only [map_add, map_mul, rs_rs] at h
      simp only [map_mul, rs_rs]
      rw [← h, ← _root_.mul_assoc, ← h']
      ring)
  let χ : ∀ a i, Γ(X, V a ⊓ N.U i) := fun a i =>
    rs X (le_inf inf_le_right (inf_le_left.trans (hV a)) : V a ⊓ N.U i ≤ N.U i ⊓ M.U (c a))
      ((wu w i (c a))⁻¹).val * ψ (a, i)
  have hχ : ∀ a b i j (W : X.Opens) (ha : W ≤ V a) (hb : W ≤ V b) (hi : W ≤ N.U i) (hj : W ≤ N.U j),
      rs X (le_inf ha hb : W ≤ V a ⊓ V b) (φ a b) =
        rs X (le_inf ha hi : W ≤ V a ⊓ N.U i) (χ a i) -
          rs X (le_inf (ha.trans (hV a)) (hb.trans (hV b)) : W ≤ M.U (c a) ⊓ M.U (c b))
            (M.g (c a) (c b)).val * rs X (le_inf hb hj : W ≤ V b ⊓ N.U j) (χ b j) := by
    intro a b i j W ha hb hi hj
    have h := congrArg (rs X (le_inf (le_inf ha hi) (le_inf hb hj) :
      W ≤ V a ⊓ N.U i ⊓ (V b ⊓ N.U j))) (hψ (a, i) (b, j))
    have h' := iso_rel w hw i j (c a) (c b) hi hj (ha.trans (hV a)) (hb.trans (hV b))
    have u1 := rs_inv_mul (le_inf hi (ha.trans (hV a)) : W ≤ N.U i ⊓ M.U (c a)) (wu w i (c a))
    have u2 := rs_inv_mul (le_inf hj (hb.trans (hV b)) : W ≤ N.U j ⊓ M.U (c b)) (wu w j (c b))
    simp only [map_sub, map_mul, rs_rs] at h
    simp only [χ, map_mul, rs_rs]
    generalize rs X _ (φ a b) = F at *
    generalize rs X _ (ψ (a, i)) = A at *
    generalize rs X _ (ψ (b, j)) = B at *
    generalize rs X _ (wu w i (c a)).val = u at *
    generalize rs X _ (wu w j (c b)).val = v at *
    generalize rs X _ ((wu w i (c a))⁻¹).val = u' at *
    generalize rs X _ ((wu w j (c b))⁻¹).val = v' at *
    generalize rs X _ (M.g (c a) (c b)).val = m at *
    generalize rs X _ (N.g i j).val = n at *
    linear_combination u' * h - F * u1 + u' * v' * B * h' - m * v' * B * u1 + u' * n * B * u2
  have hg : ∀ a, ∃ s : Γ(X, V a), ∀ i, rs X (inf_le_left : V a ⊓ N.U i ≤ V a) s = χ a i := fun a => by
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V a ⊓ N.U i) (V a)
      (fun i => homOfLE inf_le_left) (hcov _) (χ a) (fun i j => by
        have h := hχ a a i j (V a ⊓ N.U i ⊓ (V a ⊓ N.U j)) (inf_le_left.trans inf_le_left)
          (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
          (inf_le_right.trans inf_le_right)
        rw [hφ0, map_zero, rs_g_self hM, _root_.one_mul] at h
        exact sub_eq_zero.1 h.symm)
    exact ⟨s, hs⟩
  choose s hs using hg
  refine ⟨s, fun a b => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V a ⊓ V b ⊓ N.U i) (V a ⊓ V b)
    (fun i => homOfLE inf_le_left) (hcov _) _ _ fun i => ?_
  have h := hχ a b i i (V a ⊓ V b ⊓ N.U i) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right inf_le_right
  change rs X (inf_le_left : V a ⊓ V b ⊓ N.U i ≤ V a ⊓ V b) _ =
    rs X (inf_le_left : V a ⊓ V b ⊓ N.U i ≤ V a ⊓ V b) _
  rw [← hs, ← hs] at h
  simp only [rs_rs] at h
  simp only [map_sub, map_mul, rs_rs]
  exact h
end GlobalTheory.AbLaw.H1Iso
