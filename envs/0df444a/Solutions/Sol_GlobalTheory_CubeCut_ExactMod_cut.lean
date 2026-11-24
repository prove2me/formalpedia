-- Prove2me | solution 1 for GlobalTheory.CubeCut.ExactMod.cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:20:48.665111+00:00
-- url     : https://prove2.me/submissions/32c02a5b-5876-424e-bc18-b91953ca5bc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
import Theorems.Thm_GlobalTheory_CubeCut_d_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory GlobalTheory
namespace GlobalTheory
namespace CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
private theorem exists_term_d_sub_termMap_mem {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) {k : ℕ} (x : Cube.Term B k)
    (hx : ∀ s, Cube.d B k x s ∈ J s.1) :
    ∃ a₁ : Cube.Term A k, ∀ s, Cube.d B k (x - Cube.termMap φ k a₁) s ∈ JB s.1 := by
  have hx' : ∀ t : {s : Finset I // s.card = k + 1},
      ∃ a : A.obj t.1, Cube.d B k x t - (φ.app t.1).hom a ∈ JB t.1 := by
    intro t
    have h1 := hx t
    rw [hJ, Submodule.mem_sup] at h1
    obtain ⟨u, hu, _, ⟨a, rfl⟩, hua⟩ := h1
    refine ⟨a, ?_⟩
    rw [← hua, add_sub_cancel_right]
    exact hu
  choose a ha using hx'
  have hb : ∀ t, (Cube.d B k x - Cube.termMap φ (k + 1) a) t ∈ JB t.1 := fun t => by
    simpa using ha t
  have hda : ∀ u, Cube.d A (k + 1) a u ∈ JA u.1 := by
    intro u
    apply hinj u.1 (Finset.card_pos.1 (by rw [u.2]; omega))
    have h1 := congrFun (Cube.termMap_d φ (k + 1) a) u
    simp only [Cube.termMap_apply] at h1
    have h2 : (φ.app u.1).hom (Cube.d A (k + 1) a u) =
        -Cube.d B (k + 1) (Cube.d B k x - Cube.termMap φ (k + 1) a) u := by
      rw [h1, map_sub, Cube.d_d]
      simp
    rw [h2]
    exact neg_mem (d_mem hJB hb u)
  obtain ⟨a₁, ha₁⟩ := hA.2 k a hda
  refine ⟨a₁, fun s => ?_⟩
  have h1 : Cube.d B k (x - Cube.termMap φ k a₁) s =
      (Cube.d B k x - Cube.termMap φ (k + 1) a) s + (φ.app s.1).hom ((a - Cube.d A k a₁) s) := by
    rw [map_sub, ← Cube.termMap_d]
    simp only [Pi.sub_apply, Cube.termMap_apply, map_sub]
    abel
  rw [h1]
  exact add_mem (hb s) (hφ _ _ (ha₁ s))
section Family
variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))
end Family
end CubeCut
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open GlobalTheory.CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
namespace GlobalTheory.CubeCut
namespace ExactMod
theorem _root_.solution {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA) (hB : ExactMod B JB)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) : ExactMod B J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    have h1 := hB.1 _ ha₁ s
    have h2 : x s = (x - Cube.termMap φ 0 a₁) s + (φ.app s.1).hom (a₁ s) := by simp
    rw [h2, hJ]
    exact Submodule.add_mem_sup h1 (LinearMap.mem_range_self _ _)
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    obtain ⟨y, hy⟩ := hB.2 p _ ha₁
    refine ⟨y, fun s => ?_⟩
    have h2 : (x - Cube.d B p y) s =
        (x - Cube.termMap φ (p + 1) a₁ - Cube.d B p y) s + (φ.app s.1).hom (a₁ s) := by
      simp only [Pi.sub_apply, Cube.termMap_apply]
      abel
    rw [h2, hJ]
    exact Submodule.add_mem_sup (hy s) (LinearMap.mem_range_self _ _)
end ExactMod
end GlobalTheory.CubeCut
