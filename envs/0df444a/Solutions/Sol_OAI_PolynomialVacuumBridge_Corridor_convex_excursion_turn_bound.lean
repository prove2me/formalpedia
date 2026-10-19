-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:15:15.752836+00:00
-- url     : https://prove2.me/submissions/11cdc882-7c69-4caa-93c0-fc9ef48a62dc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryArcs.lean:L213-L247
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_IsExcursion_distinct_ports
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_box_two_faces
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_outside_boundary_germ
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_simple_polygon_signed_turn
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_star_boundary_cycle_turn
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_star_boundary_endpoint
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index

-- ---- from OAI.Combinatorics.HoneycombCorridor.Polygons ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem simple_polygon_turning : SimplePolygonTurning := by
  intro g w hne hN hc
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g w hne hN hc
  have hsum := simple_polygon_signed_turn g w hne hN hc p ε hp hpne hε hvals
  rcases hε with rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

namespace Polygon
end Polygon

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Convexity ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem admissiblyConvex_box (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    ∃ lo hi : Fin 3 → ℤ, ∀ v, v ∈ D ↔ BoxMem lo hi v := by
  obtain ⟨lo,hi,h⟩ := hD
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact integer_bounds_fraction _ _ _ _ ha ha'

theorem mem_starFaces (D : Finset Vertex) (a : FaceIndex) :
    a ∈ starFaces D ↔ ∃ v ∈ faceVertices a, v ∈ D := by
  simp only [starFaces,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    mem_faceVertices]
  aesop

theorem incident_mem_starFaces {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    (k : Fin 3) : leftFace (v,k) ∈ starFaces D := by
  apply (mem_starFaces D _).mpr
  exact ⟨v,(mem_faceVertices _ _).mpr ⟨k,rfl⟩,hv⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.FaceBoundary ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem faceBoundary_germ_unique (S : Finset FaceIndex) (v : Vertex) (k l : Fin 3)
    (hk : OnFaceBoundary S (v,k)) (hl : OnFaceBoundary S (v,l)) : k = l := by
  simp only [OnFaceBoundary,rightFace_prev] at hk hl
  fin_cases k <;> fin_cases l <;> norm_num at hk hl ⊢ <;> tauto

theorem faceBoundary_vertex_injective (S : Finset FaceIndex) :
    Function.Injective (fun g : FaceBoundary S => g.val.1) := by
  intro ⟨⟨v,k⟩,hk⟩ ⟨⟨u,l⟩,hl⟩ he
  dsimp at he
  subst u
  have := faceBoundary_germ_unique S v k l hk hl
  subst l
  rfl

theorem faceBoundaryNext_injective (S : Finset FaceIndex) :
    Function.Injective (faceBoundaryNext S) := by
  intro g h he
  apply faceBoundary_vertex_injective S
  have hval := congrArg Subtype.val he
  have hv := congrArg (fun d : Germ => neighbor d.1 d.2) hval
  simpa only [faceBoundaryNext,advance,neighbor_neighbor] using hv

theorem faceBoundaryWord_terminal (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    terminalGerm g.val (faceBoundaryWord S g n) = ((faceBoundaryNext S)^[n] g).val := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [faceBoundaryWord,terminalGerm,Function.iterate_succ_apply]
    exact ih (faceBoundaryNext S g)

theorem faceBoundaryWord_traced (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    traced g.val (faceBoundaryWord S g n) =
      List.ofFn (fun i : Fin n => ((faceBoundaryNext S)^[i.val] g).val.1) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    simp only [faceBoundaryWord,traced,List.ofFn_succ,Fin.val_zero,Function.iterate_zero,
      id_eq,Fin.val_succ,Function.iterate_succ_apply]
    congr 1
    exact ih (faceBoundaryNext S g)

theorem faceBoundary_closed_word (S : Finset FaceIndex) (g : FaceBoundary S) :
    ∃ n : ℕ, 0 < n ∧ (traced g.val (faceBoundaryWord S g n)).Nodup ∧
      terminalGerm g.val (faceBoundaryWord S g n) = g.val := by
  let n := Function.minimalPeriod (faceBoundaryNext S) g
  refine ⟨n,Function.minimalPeriod_pos_of_mem_periodicPts
    ((faceBoundaryNext_injective S).mem_periodicPts g),?_,?_⟩
  · rw [faceBoundaryWord_traced,List.nodup_ofFn]
    intro i j he
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
    exact faceBoundary_vertex_injective S he
  · rw [faceBoundaryWord_terminal,Function.iterate_minimalPeriod]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryCharge ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem star_boundary_outside (D : Finset Vertex) (g : FaceBoundary (starFaces D)) :
    g.val.1 ∉ D := by
  intro hv
  exact g.property.1 (incident_mem_starFaces hv g.val.2)

theorem star_boundary_no_double_negative (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (hg : faceBoundaryTurn (starFaces D) g.val = false) :
    faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val = true := by
  classical
  by_contra hn
  have hn' : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val =
      false := by
    cases he : (faceBoundaryTurn (starFaces D)
      (faceBoundaryNext (starFaces D) g).val) <;> simp_all
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp g.property.2
  have hs_mem := (faceBoundaryTurn_false _ _).mp hn'
  have hs_mem' : leftFace (neighbor g.val.1 (g.val.2+1),g.val.2+2) ∈ starFaces D := by
    simpa [faceBoundaryNext,hg,advance,outgoingSlot,add_assoc] using hs_mem
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hs_mem'
  rcases box_two_faces lo hi g.val.1 r s g.val.2 hr hs ((hbox _).mp hr')
    ((hbox _).mp hs') with h | h
  · exact star_boundary_outside D g ((hbox _).mpr h)
  · apply star_boundary_outside D (faceBoundaryNext (starFaces D) g)
    simpa only [faceBoundaryNext,advance,hg,outgoingSlot,Bool.false_eq_true,ite_false]
      using (hbox _).mpr h

theorem star_boundary_turn_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) :
    boundaryCharge (starFaces D) (faceBoundaryNext (starFaces D) g) -
      boundaryCharge (starFaces D) g ≤ turnUnit (faceBoundaryTurn (starFaces D) g.val) := by
  cases hg : faceBoundaryTurn (starFaces D) g.val
  · have hn := star_boundary_no_double_negative D hD g hg
    simp [boundaryCharge,hg,hn,turnUnit]
  · cases hn : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val <;>
      simp [boundaryCharge,hg,hn,turnUnit]

theorem star_boundary_word_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    boundaryCharge (starFaces D) ((faceBoundaryNext (starFaces D))^[n] g) -
      boundaryCharge (starFaces D) g ≤ turnUnits (faceBoundaryWord (starFaces D) g n) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,turnUnits]
  | succ n ih =>
    have h₁ := star_boundary_turn_charge D hD g
    have h₂ := ih (faceBoundaryNext (starFaces D) g)
    simp only [faceBoundaryWord,turnUnits,List.map_cons,List.sum_cons,
      Function.iterate_succ_apply] at *
    omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryContainment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem star_boundary_trace_outside (D : Finset Vertex)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    ∀ v ∈ traced g.val (faceBoundaryWord (starFaces D) g n), v ∉ D := by
  intro v hv
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hv
  obtain ⟨i,rfl⟩ := hv
  exact star_boundary_outside D _

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryArcs ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem chord_close_trace (g h e : Germ) (B w : List Bool)
    (hb : terminalGerm h (false :: B) = g)
    (he : terminalGerm e w = stemGerm h false) :
    traced e (w ++ (true :: B) ++ [true]) =
      traced e w ++ (traced h (false :: B) ++ [g.1]) := by
  simp only [traced_append,terminalGerm_append,he]
  have htr := stem_forward_trace h false B
  have htm := stem_forward_terminal h false B
  simp only [Bool.not_false] at htr htm
  rw [htr,htm,hb]
  simp [traced,List.append_assoc]

theorem chord_close_terminal (g h e : Germ) (B w : List Bool)
    (hb : terminalGerm h (false :: B) = g)
    (he : terminalGerm e w = stemGerm h false) (he' : e = advance g true) :
    terminalGerm e (w ++ (true :: B) ++ [true]) = e := by
  simp only [terminalGerm_append,he]
  have htm := stem_forward_terminal h false B
  simp only [Bool.not_false] at htm
  rw [htm,hb]
  simpa only [terminalGerm] using he'.symm

theorem chord_close_turn (g : Germ) (A B : List Bool) (e : Germ) (w : List Bool)
    (hN : (traced g ((false :: A) ++ (false :: B))).Nodup)
    (hc : terminalGerm g ((false :: A) ++ (false :: B)) = g)
    (he : e = advance g true)
    (ht : terminalGerm e w = stemGerm (terminalGerm g (false :: A)) false)
    (hwN : (traced e w).Nodup)
    (hd : ∀ v ∈ traced e w, v ∉ traced g ((false :: A) ++ (false :: B))) :
    turnUnits w + turnUnits (false :: B) + 3 = 6 ∨
      turnUnits w + turnUnits (false :: B) + 3 = -6 := by
  let h := terminalGerm g (false :: A)
  have hb : terminalGerm h (false :: B) = g := by
    exact (terminalGerm_append g (false :: A) (false :: B)).symm.trans hc
  have hN' : (g.1 :: (traced (advance g false) A ++ traced h (false :: B))).Nodup := by
    simpa only [h,traced_append,traced,terminalGerm,List.cons_append] using hN
  have hgnot : g.1 ∉ traced h (false :: B) := by
    intro hm
    exact (List.nodup_cons.mp hN').1 (List.mem_append_right _ hm)
  have hBN : (traced h (false :: B)).Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp hN').2).2.1
  have hBN' : (traced h (false :: B) ++ [g.1]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hBN,by simp,?_⟩
    intro a ha b hb hab
    have hb' := List.mem_singleton.mp hb
    exact hgnot ((hab.trans hb') ▸ ha)
  have hsub : ∀ v ∈ traced h (false :: B) ++ [g.1],
      v ∈ traced g ((false :: A) ++ (false :: B)) := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rw [traced_append]
      exact List.mem_append_right _ hv
    · have heq := List.mem_singleton.mp hv
      subst v
      simp [traced_append,traced]
  have hjoinN : (traced e (w ++ (true :: B) ++ [true])).Nodup := by
    rw [chord_close_trace g h e B w hb ht]
    apply List.nodup_append.mpr
    refine ⟨hwN,hBN',?_⟩
    intro a ha b hb hab
    subst b
    exact hd a ha (hsub a hb)
  have hjoinC := chord_close_terminal g h e B w hb ht he
  have hn : w ++ (true :: B) ++ [true] ≠ [] := by simp
  have h := simple_polygon_turning e _ hn hjoinN hjoinC
  have heq : turnUnits (w ++ (true :: B) ++ [true]) =
      turnUnits w + turnUnits (false :: B) + 3 := by
    simp [turnUnit,turnUnits]
    ring
  rwa [heq] at h

theorem cycle_chord_turn_bound (g : Germ) (A B : List Bool) (e : Germ) (w : List Bool)
    (hN : (traced g ((false :: A) ++ (false :: B))).Nodup)
    (hc : terminalGerm g ((false :: A) ++ (false :: B)) = g)
    (he : e = advance g true)
    (ht : terminalGerm e w = stemGerm (terminalGerm g (false :: A)) false)
    (hwN : (traced e w).Nodup)
    (hd : ∀ v ∈ traced e w, v ∉ traced g ((false :: A) ++ (false :: B)))
    (hturn : turnUnits ((false :: A) ++ (false :: B)) = 6)
    (hA : 0 ≤ turnUnits (false :: A)) (hB : 0 ≤ turnUnits (false :: B)) :
    -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 := by
  have h₁ := chord_close_turn g A B e w hN hc he ht hwN hd
  let h := terminalGerm g (false :: A)
  let e' := reverseGerm (terminalGerm e w)
  have hrot := closed_word_rotate g (false :: A) (false :: B) hN hc
  have hback : terminalGerm h (false :: B) = g := by
    exact (terminalGerm_append g (false :: A) (false :: B)).symm.trans hc
  have he' : e' = advance h true := by simp only [e',ht,reverse_stem_false]; rfl
  have ht' : terminalGerm e' (reverseTurns w) =
      stemGerm (terminalGerm h (false :: B)) false := by
    rw [hback]
    simp only [e',terminalGerm_reverse,he,reverse_advance_true]
  have hwN' : (traced e' (reverseTurns w)).Nodup := by
    simpa only [e',traced_reverse,List.nodup_reverse] using hwN
  have hd' : ∀ v ∈ traced e' (reverseTurns w),
      v ∉ traced h ((false :: B) ++ (false :: A)) := by
    intro v hv hmem
    have hv' : v ∈ traced e w := by simpa only [e',traced_reverse,List.mem_reverse] using hv
    apply hd v hv'
    rw [traced_append,hback] at hmem
    rw [traced_append]
    exact List.mem_append.mpr (List.mem_append.mp hmem |>.symm)
  have h₂ := chord_close_turn h B A e' (reverseTurns w) hrot.1 hrot.2.1
    he' ht' hwN' hd'
  rw [turnUnits_reverse] at h₂
  rw [turnUnits_append] at hturn
  omega

theorem faceBoundaryWord_append (S : Finset FaceIndex) (g : FaceBoundary S) (m n : ℕ) :
    faceBoundaryWord S g (m+n) = faceBoundaryWord S g m ++
      faceBoundaryWord S ((faceBoundaryNext S)^[m] g) n := by
  induction m generalizing g with
  | zero => simp [faceBoundaryWord]
  | succ m ih =>
    simp only [Nat.succ_add,faceBoundaryWord,List.cons_append,Function.iterate_succ_apply]
    rw [ih]

theorem convex_distinct_outer_vertices (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    (terminalGerm e.1 e.2).1 ≠ (reverseGerm e.1).1 := by
  intro hv
  have hstart := (outside_boundary_germ D hD (reverseGerm e.1).1 e.1.2 he.2.1
    (by simpa only [reverseGerm,neighbor_neighbor] using he.1)).1
  have hend := (outside_boundary_germ D hD (terminalGerm e.1 e.2).1
    (terminalGerm e.1 e.2).2 he.2.2.2 he.reverse.1).1
  rw [hv] at hend
  have hk := faceBoundary_germ_unique (starFaces D) (reverseGerm e.1).1
    ((terminalGerm e.1 e.2).2+1) (e.1.2+1) hend hstart
  have hk' : (terminalGerm e.1 e.2).2 = e.1.2 := add_right_cancel hk
  have heq : terminalGerm e.1 e.2 = reverseGerm e.1 := Prod.ext hv hk'
  apply he.distinct_ports
  rw [heq,reverseGerm_reverseGerm]

theorem boundary_chord_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (i : ℕ) (hi : 0 < i) (hin : i < n)
    (hgi : faceBoundaryTurn (starFaces D) ((faceBoundaryNext (starFaces D))^[i] g).val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (ht : terminalGerm e w = stemGerm ((faceBoundaryNext (starFaces D))^[i] g).val false)
    (hwN : (traced e w).Nodup) (hd : ∀ v ∈ traced e w, v ∈ D) :
    -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 := by
  let G := (faceBoundaryNext (starFaces D))^[i] g
  have hn : 0 < n := lt_trans hi hin
  have hperiod : (faceBoundaryNext (starFaces D))^[n] g = g := by
    apply Subtype.ext
    rwa [faceBoundaryWord_terminal] at hc
  have hend : (faceBoundaryNext (starFaces D))^[n-i] G = g := by
    simp only [G,← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hin),hperiod]
  have hAi := star_boundary_word_charge D hD g i
  have hBi := star_boundary_word_charge D hD G (n-i)
  simp only [G,hgi,hg,hend,boundaryCharge,Bool.false_eq_true,ite_false,sub_self] at hAi hBi
  obtain ⟨a,hai⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  obtain ⟨b,hbi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hin))
  let A := faceBoundaryWord (starFaces D) (faceBoundaryNext (starFaces D) g) a
  let B := faceBoundaryWord (starFaces D) (faceBoundaryNext (starFaces D) G) b
  have hA : faceBoundaryWord (starFaces D) g i = false :: A := by
    rw [hai,faceBoundaryWord,hg]
  have hB : faceBoundaryWord (starFaces D) G (n-i) = false :: B := by
    rw [hbi,faceBoundaryWord,hgi]
  have hW : faceBoundaryWord (starFaces D) g n = (false :: A) ++ (false :: B) := by
    conv_lhs => rw [← Nat.add_sub_cancel' (Nat.le_of_lt hin)]
    rw [faceBoundaryWord_append,hA,hB]
  have hterminal : terminalGerm g.val (false :: A) = G.val := by
    rw [← hA,faceBoundaryWord_terminal]
  apply cycle_chord_turn_bound g.val A B e w (by rwa [← hW]) (by rwa [← hW]) he
    (by rwa [hterminal]) hwN
  · intro v hv hm
    rw [← hW] at hm
    exact star_boundary_trace_outside D g n v hm (hd v hv)
  · rw [← hW]
    exact star_boundary_cycle_turn D hD g n hn hN hc
  · rwa [← hA]
  · rwa [← hB]

theorem convex_excursion_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    -3 ≤ turnUnits e.2 ∧ turnUnits e.2 ≤ 3 := by
  classical
  have hs := outside_boundary_germ D hD (reverseGerm e.1).1 e.1.2 he.2.1
    (by simpa only [reverseGerm,neighbor_neighbor] using he.1)
  let g : FaceBoundary (starFaces D) := ⟨((reverseGerm e.1).1,e.1.2+1),hs.1⟩
  have hge : e.1 = advance g.val true := by
    change e.1 = advance ((reverseGerm e.1).1,e.1.2+1) true
    rw [boundary_inward_port]
    exact (reverseGerm_reverseGerm e.1).symm
  obtain ⟨n,hn,hN,hc⟩ := faceBoundary_closed_word (starFaces D) g
  obtain ⟨hwN,hwD⟩ := stopped_traced D e.1 e.2 he.2.2.1
  have hm := star_boundary_endpoint D hD g n hn hN hc hs.2 e.1 e.2 hge hwD
    he.2.2.2 he.reverse.1
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hm
  obtain ⟨i,hi⟩ := hm
  have hi0 : 0 < i.val := by
    by_contra hn
    have hz : i.val = 0 := by omega
    have hv : (terminalGerm e.1 e.2).1 = (reverseGerm e.1).1 := by
      simpa only [hz,Function.iterate_zero,id_eq,g] using hi.symm
    exact convex_distinct_outer_vertices D hD e he hv
  have hu := outside_boundary_germ D hD (terminalGerm e.1 e.2).1
    (terminalGerm e.1 e.2).2 he.2.2.2 he.reverse.1
  let u : FaceBoundary (starFaces D) :=
    ⟨((terminalGerm e.1 e.2).1,(terminalGerm e.1 e.2).2+1),hu.1⟩
  have hiu : (faceBoundaryNext (starFaces D))^[i.val] g = u :=
    faceBoundary_vertex_injective (starFaces D) hi
  apply boundary_chord_turn_bound D hD g n hN hc hs.2 i.val hi0 i.isLt
    (by rw [hiu]; exact hu.2) e.1 e.2 hge _ hwN hwD
  rw [hiu]
  change terminalGerm e.1 e.2 = stemGerm
    ((terminalGerm e.1 e.2).1,(terminalGerm e.1 e.2).2+1) false
  exact (boundary_stem_port _ _).symm

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound := @_root_.OAI.PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound
