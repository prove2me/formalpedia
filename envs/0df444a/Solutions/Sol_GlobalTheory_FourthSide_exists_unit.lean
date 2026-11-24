-- Prove2me | solution 1 for GlobalTheory.FourthSide.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:00.388939+00:00
-- url     : https://prove2.me/submissions/e41660f8-fe0f-459b-8db4-2509edc1edd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
import Theorems.Thm_GlobalTheory_FourthSide_germ_change
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FourthSide
variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}
namespace GlobalTheory.FourthSide
theorem _root_.solution (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    (jM' : M'.ι) (jL' : L'.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jL : L.ι), Φ (pG' (r z)) ∈ M.U jM →
        pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gm r z _ s = germ pG' fG' h w wL we r z jM jM' jL jL' := by
  have p₁ : ∀ x, pG (h x) = Φ (pG' x) := fun x => congrArg (fun g => g x) e₁.symm
  have p₂ : ∀ x, fG (h x) = Ψ (fG' x) := fun x => congrArg (fun g => g x) e₂
  obtain ⟨W, hW⟩ : ∃ W : M.ι × L.ι → Ge'.Opens, ∀ i x, x ∈ W i ↔
      Φ (pG' x) ∈ M.U i.1 ∧ pG' x ∈ M'.U jM' ∧ Ψ (fG' x) ∈ L.U i.2 ∧ fG' x ∈ L'.U jL' :=
    ⟨fun i => pG' ⁻¹ᵁ (Φ ⁻¹ᵁ M.U i.1) ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ (fG' ⁻¹ᵁ (Ψ ⁻¹ᵁ L.U i.2) ⊓ fG' ⁻¹ᵁ L'.U jL')),
      fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  have l₁ : ∀ i, W i ≤ pG' ⁻¹ᵁ ((M.pull Φ).U (fun _ => i.1) ⊓ M'.U jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
  have l₂ : ∀ i, W i ≤ h ⁻¹ᵁ ((M.pull pG).U (fun _ => i.1) ⊓ (L.pull fG).U (fun _ => i.2)) := fun i x hx =>
    ⟨mem_pull.2 ((p₁ x).symm ▸ ((hW i x).1 hx).1), mem_pull.2 ((p₂ x).symm ▸ ((hW i x).1 hx).2.2.1)⟩
  have l₃ : ∀ i, W i ≤ fG' ⁻¹ᵁ ((L.pull Ψ).U (fun _ => i.2) ⊓ L'.U jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Ge', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (i : M.ι × L.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ pG' fG' h w wL we r z i.1 jM' i.2 jL' :=
    ⟨fun i => (res (l₁ i) (pullU pG' _ (w.s (fun _ => i.1, jM'))))⁻¹ *
        (res (l₂ i) (pullU h _ (we.s (fun _ => i.1, fun _ => i.2))) *
          res (l₃ i) (pullU fG' _ (wL.s (fun _ => i.2, jL')))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ i) hz _).trans (gm_pull r pG' z _ (l₁ i hz) _)))) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r h z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r fG' z _ (l₃ i hz) _)))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' x))
      obtain ⟨j, hj⟩ := exists_chart hL (Ψ (fG' x))
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨hi, mem_pull.1 hx.1, hj, mem_pull.1 hx.2⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwL hwe (𝟙 Ge') x i.1 i'.1 jM' jM' i.2 i'.2 jL' jL' h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, gm_self hL' (𝟙 Ge' ≫ fG') x h₁.2.2.2, inv_one, one_mul, one_mul] at k
      exact (hu _ (𝟙 Ge') x i hx.1).trans (k.trans (hu _ (𝟙 Ge') x i' hx.2).symm))
  refine ⟨s, fun Z r z jM jL a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jM, jL) (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jM, jL)) hz s).symm.trans
    ((congrArg (gm r z (W (jM, jL))) (hs (jM, jL))).trans (hu Z r z (jM, jL) hz))
end GlobalTheory.FourthSide
