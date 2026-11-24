-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_locSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:03:01.37343+00:00
-- url     : https://prove2.me/submissions/70fe7b5f-0122-4316-bada-3cf8ab2938e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_pow
import Theorems.Thm_GlobalTheory_LinDescent_gs_sub
import Theorems.Thm_GlobalTheory_LinDescent_gs_zero
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_LinDescent_gs_g
import Theorems.Thm_GlobalTheory_LinDescent_glue_sec
import Theorems.Thm_GlobalTheory_LinDescent_eventually_extend
import Theorems.Thm_GlobalTheory_LinDescent_eventually_kill
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.LinDescent
theorem _root_.solution {L : LB X} (hL : L.IsLB) {W : X.Opens} (hW : IsAffineOpen W) (x : X)
    (hx : x ∈ W) : ∃ m : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W m ∧
      ∀ i, x ∈ L.U i → x ∈ X.basicOpen (m i) := by
  classical
  have H : ∀ w : W, ∃ (a : L.ι) (h : Γ(X, W)), X.basicOpen h ≤ L.U a ∧ w.1 ∈ X.basicOpen h :=
    fun w => by
      obtain ⟨a, ha⟩ := exists_chart hL w.1
      obtain ⟨h, h1, h2⟩ := hW.exists_basicOpen_le (V := L.U a) ⟨w.1, ha⟩ w.2
      exact ⟨a, h, h1, h2⟩
  choose a h ha hh using H
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun w : W => (X.basicOpen (h w) : Set X))
    (fun w => (X.basicOpen (h w)).isOpen) fun w hw => Set.mem_iUnion.2 ⟨⟨w, hw⟩, hh _⟩
  have hc : ∀ y ∈ W, ∃ k : s, y ∈ X.basicOpen (h k) := fun y hy => by
    obtain ⟨k, hk, hk'⟩ := Set.mem_iUnion₂.1 (hs hy)
    exact ⟨⟨k, hk⟩, hk'⟩
  let D : s → X.Opens := fun k => X.basicOpen (h k)
  have hDW : ∀ k, D k ≤ W := fun k => X.basicOpen_le _
  have hD : ∀ k, IsAffineOpen (D k) := fun k => hW.basicOpen _
  have hDD : ∀ k l, IsAffineOpen (D k ⊓ D l) := fun k l => by
    rw [← Scheme.basicOpen_mul]; exact hW.basicOpen _
  let x₀ : W := ⟨x, hx⟩
  let f := h x₀
  have hb : ∀ {V : X.Opens} (e : V ≤ W), X.basicOpen (rs e f) = V ⊓ X.basicOpen f :=
    fun e => X.basicOpen_res f (homOfLE e).op
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 fun k : s => eventually_extend (hD k) (rs (hDW k) f)
    (V := L.U (a k) ⊓ L.U (a x₀)) ((hb _).le.trans (inf_le_inf (ha k) (ha x₀)))
    (L.g (a k) (a x₀)).val).exists
  choose b hb' using hN
  have hb'' : ∀ k y, y ∈ D k → y ∈ X.basicOpen f → gs (𝟙 X) y (D k) (b k) =
      gs (𝟙 X) y W f ^ N * (gg L (𝟙 X) y (a k) (a x₀)).val := fun k y h1 h2 => by
    rw [hb' k y ((hb _).ge ⟨h1, h2⟩), gs_res _ y _ h1, gs_g L (𝟙 X) y (ha k h1) (ha x₀ h2)]
  have v : ∀ k l y, y ∈ D k ⊓ D l → gs (𝟙 X) y (D k ⊓ D l) (rs inf_le_left (b k) -
      rs (inf_le_inf (ha k) (ha l)) (L.g (a k) (a l)).val * rs inf_le_right (b l)) =
      gs (𝟙 X) y (D k) (b k) - (gg L (𝟙 X) y (a k) (a l)).val * gs (𝟙 X) y (D l) (b l) :=
    fun k l y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_g L (𝟙 X) y (ha k hy.1) (ha l hy.2)]
  obtain ⟨N', hN'⟩ := (Filter.eventually_all.2 fun p : s × s => eventually_kill (hDD p.1 p.2)
    (rs (inf_le_left.trans (hDW _)) f) (rs inf_le_left (b p.1) -
      rs (inf_le_inf (ha p.1) (ha p.2)) (L.g (a p.1) (a p.2)).val * rs inf_le_right (b p.2))
    (fun y hy => by
      have hy' := (hb _).le hy
      rw [v _ _ y hy'.1, hb'' _ y hy'.1.1 hy'.2, hb'' _ y hy'.1.2 hy'.2, mul_left_comm,
        ← Units.val_mul, gm_cocycle hL (𝟙 X) y (ha _ hy'.1.1) (ha _ hy'.1.2) (ha _ hy'.2),
        sub_self])).exists
  have v' : ∀ k y, y ∈ D k → gs (𝟙 X) y (D k) (rs (hDW k) f ^ N' * b k) =
      gs (𝟙 X) y W f ^ N' * gs (𝟙 X) y (D k) (b k) := fun k y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨m, hm, hm'⟩ := glue_sec hL W D (fun k => a k) hDW (fun k => ha k) hc
    (fun k => rs (hDW k) f ^ N' * b k) (fun k l y hk hl => by
      have hy : y ∈ D k ⊓ D l := ⟨hk, hl⟩
      have e := congrArg (gs (𝟙 X) y (D k ⊓ D l)) (hN' (k, l))
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, v k l y hy, gs_zero _ y _ hy,
        mul_sub, sub_eq_zero] at e
      rw [v' k y hk, v' l y hl, e, mul_left_comm])
  refine ⟨m, hm, fun i hi => ?_⟩
  obtain ⟨k, hk⟩ := hc x hx
  have hf : IsUnit (gs (𝟙 X) x W f) := (isUnit_gs_iff _ x W hx f).2 (hh x₀)
  refine (isUnit_gs_iff (𝟙 X) x (W ⊓ L.U i) ⟨hx, hi⟩ _).1 ?_
  rw [hm' _ _ x i k hi hk, v' k x hk, hb'' k x hk (hh x₀)]
  exact (Units.isUnit _).mul ((hf.pow _).mul ((hf.pow _).mul (Units.isUnit _)))
end GlobalTheory.LinDescent
