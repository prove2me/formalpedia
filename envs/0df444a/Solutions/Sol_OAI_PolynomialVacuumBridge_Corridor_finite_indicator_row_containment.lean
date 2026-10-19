-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.finite_indicator_row_containment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:09:44.456916+00:00
-- url     : https://prove2.me/submissions/029d55ba-d66b-45aa-ad1d-2bbaa014ff01

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryContainment.lean:L64-L113
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.finite_indicator_row_containment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryContainment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem finite_indicator_row_containment (p : FaceIndex →₀ ℤ) (S : Finset FaceIndex)
    (hval : ∀ a, p a = 0 ∨ p a = 1)
    (hgrad : ∀ i j : ℤ, p (i,j) ≠ p (i-1,j) →
      p (i,j) - p (i-1,j) = faceIndicator S (i,j) - faceIndicator S (i-1,j))
    (hrow : ∀ i₁ i i₂ j : ℤ, i₁ ≤ i → i ≤ i₂ → (i₁,j) ∈ S → (i₂,j) ∈ S →
      (i,j) ∈ S) : p.support ⊆ S := by
  classical
  rintro ⟨i,j⟩ ha
  let R := (p.support.filter fun a => a.2 = j).image Prod.fst
  have hRmem (x : ℤ) : x ∈ R ↔ p (x,j) ≠ 0 := by
    simp only [R,Finset.mem_image,Finset.mem_filter,Finsupp.mem_support_iff]
    constructor
    · rintro ⟨⟨u,v⟩,⟨hp,hj⟩,hi⟩
      dsimp at hj hi
      subst v; subst u
      exact hp
    · intro hx
      exact ⟨(x,j),⟨hx,rfl⟩,rfl⟩
  have hi : i ∈ R := (hRmem i).mpr (Finsupp.mem_support_iff.mp ha)
  have hne : R.Nonempty := ⟨i,hi⟩
  let a := R.min' hne
  let b := R.max' hne
  have haR : a ∈ R := R.min'_mem hne
  have hbR : b ∈ R := R.max'_mem hne
  have hpa : p (a,j) = 1 := (hval _).resolve_left ((hRmem a).mp haR)
  have hpb : p (b,j) = 1 := (hval _).resolve_left ((hRmem b).mp hbR)
  have hpa' : p (a-1,j) = 0 := by
    by_contra hz
    have hm := R.min'_le (a-1) ((hRmem _).mpr hz)
    change a ≤ a-1 at hm
    omega
  have hpb' : p (b+1,j) = 0 := by
    by_contra hz
    have hm := R.le_max' (b+1) ((hRmem _).mpr hz)
    change b+1 ≤ b at hm
    omega
  have haS : (a,j) ∈ S := by
    have h := hgrad a j (by omega)
    rw [hpa,hpa'] at h
    by_contra hn
    simp only [faceIndicator,ite_eq_right hn] at h
    split_ifs at h <;> omega
  have hbS : (b,j) ∈ S := by
    have he : b+1-1 = b := by omega
    have h := hgrad (b+1) j (by rw [he,hpb,hpb']; norm_num)
    rw [he,hpb,hpb'] at h
    by_contra hn
    simp only [faceIndicator,ite_eq_right hn] at h
    split_ifs at h <;> omega
  exact hrow a i b j (R.min'_le _ hi) (R.le_max' _ hi) haS hbS

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.finite_indicator_row_containment := @_root_.OAI.PolynomialVacuumBridge.Corridor.finite_indicator_row_containment
