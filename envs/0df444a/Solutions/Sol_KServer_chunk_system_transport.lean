-- Prove2me | solution 1 for KServer.chunk_system_transport
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T13:09:04.910769+00:00
-- url     : https://prove2.me/submissions/f24b61dd-87f5-4d09-b738-14ceeb294188

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace Transport

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Push a request sequence forward along a map. -/
def mapReqs (φ : X → Y) (l : List (Set X)) : List (Set Y) :=
  l.map (fun S => φ '' S)

theorem mapReqs_append (φ : X → Y) (l l' : List (Set X)) :
    mapReqs φ (l ++ l') = mapReqs φ l ++ mapReqs φ l' := by
  unfold mapReqs
  rw [List.map_append]

theorem mapReqs_take (φ : X → Y) (l : List (Set X)) (n : ℕ) :
    mapReqs φ (l.take n) = (mapReqs φ l).take n := by
  unfold mapReqs
  rw [List.map_take]

theorem mapReqs_flatten (φ : X → Y) (L : List (List (Set X))) :
    mapReqs φ L.flatten = (L.map (mapReqs φ)).flatten := by
  unfold mapReqs
  rw [List.map_flatten]

/-- Pull an evader on `Y` back along a bijective isometry to an evader
on `X`. -/
noncomputable def pullEvader (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b)
    (E : EvaderAlgorithm Y) : EvaderAlgorithm X where
  pos l := φ.symm (E.pos (mapReqs φ l))
  serves l S hS := by
    have h1 := E.serves (mapReqs φ l) (φ '' S) (hS.image φ)
    have he : mapReqs φ (l ++ [S]) = mapReqs φ l ++ [φ '' S] := by
      rw [mapReqs_append]
      rfl
    rw [← he] at h1
    obtain ⟨x, hxS, hx⟩ := h1
    have h2 : φ.symm (E.pos (mapReqs φ (l ++ [S]))) = x := by
      rw [← hx, Equiv.symm_apply_apply]
    rw [h2]
    exact hxS

theorem pullEvader_cost (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b)
    (E : EvaderAlgorithm Y) (l : List (Set X)) :
    (pullEvader φ hφ E).cost l = E.cost (mapReqs φ l) := by
  unfold EvaderAlgorithm.cost
  have hlen : (mapReqs φ l).length = l.length := by
    unfold mapReqs
    rw [List.length_map]
  rw [hlen]
  refine Finset.sum_congr rfl fun j _ => ?_
  show dist (φ.symm (E.pos (mapReqs φ (l.take j))))
      (φ.symm (E.pos (mapReqs φ (l.take (j + 1))))) = _
  rw [mapReqs_take, mapReqs_take]
  have hsym : ∀ a b : Y, dist (φ.symm a) (φ.symm b) = dist a b := by
    intro a b
    have := hφ (φ.symm a) (φ.symm b)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  rw [hsym]

theorem pullEvader_costOn (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b)
    (E : EvaderAlgorithm Y) (h χ : List (Set X)) :
    (pullEvader φ hφ E).costOn h χ = E.costOn (mapReqs φ h) (mapReqs φ χ) := by
  unfold EvaderAlgorithm.costOn
  rw [pullEvader_cost, pullEvader_cost, mapReqs_append]

private theorem find?_congr2 {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a (List.mem_cons_self ..)]
    cases q a
    · exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    · rfl

theorem pull_bailTime (φ : X ≃ Y) (bail : List (Set Y) → Bool)
    (h χ : List (Set X)) :
    bailTime (fun l => bail (mapReqs φ l)) h χ
      = bailTime bail (mapReqs φ h) (mapReqs φ χ) := by
  unfold bailTime
  have hlen : (mapReqs φ χ).length = χ.length := by
    unfold mapReqs
    rw [List.length_map]
  rw [hlen]
  refine find?_congr2 _ _ _ fun q _ => ?_
  show bail (mapReqs φ (h ++ List.take q χ)) = _
  congr 1
  rw [mapReqs_append, mapReqs_take]

theorem pullEvader_bailCost (φ : X ≃ Y)
    (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b)
    (E : EvaderAlgorithm Y) (bail : List (Set Y) → Bool)
    (h χ : List (Set X)) (p : ℝ) :
    (pullEvader φ hφ E).bailCost (fun l => bail (mapReqs φ l)) h χ p
      = E.bailCost bail (mapReqs φ h) (mapReqs φ χ) p := by
  unfold EvaderAlgorithm.bailCost
  rw [pull_bailTime]
  rcases hq : bailTime bail (mapReqs φ h) (mapReqs φ χ) with - | q
  · rw [pullEvader_costOn]
  · show (pullEvader φ hφ E).costOn h (List.take q χ) + p
        = E.costOn (mapReqs φ h) (List.take q (mapReqs φ χ)) + p
    rw [pullEvader_costOn, mapReqs_take]

/-- Offline cost is preserved by a distance-preserving bijection. -/
theorem offline_map_eq (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b)
    (x₀ : X) (σ : List (Set X)) :
    evaderOfflineCost (φ x₀) (mapReqs φ σ) = evaderOfflineCost x₀ σ := by
  have hsym : ∀ a b : Y, dist (φ.symm a) (φ.symm b) = dist a b := by
    intro a b
    have := hφ (φ.symm a) (φ.symm b)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  have hlen : (mapReqs φ σ).length = σ.length := by
    unfold mapReqs
    rw [List.length_map]
  unfold evaderOfflineCost
  congr 1
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, ⟨hP0, hPs⟩, hc⟩
    refine ⟨fun j => φ.symm (P j), ⟨by
      show φ.symm (P 0) = x₀
      rw [hP0, Equiv.symm_apply_apply], ?_⟩, ?_⟩
    · intro j hne
      have hj : (j : ℕ) < (mapReqs φ σ).length := by
        rw [hlen]
        exact j.isLt
      have hget : (mapReqs φ σ).get ⟨(j : ℕ), hj⟩ = φ '' (σ.get j) := by
        unfold mapReqs
        simp [List.getElem_map]
      have h1 := hPs ⟨(j : ℕ), hj⟩ (by rw [hget]; exact hne.image φ)
      rw [hget] at h1
      obtain ⟨x, hxS, hx⟩ := h1
      show φ.symm (P ((j : ℕ) + 1)) ∈ σ.get j
      rw [← hx, Equiv.symm_apply_apply]
      exact hxS
    · rw [hc, hlen]
      exact Finset.sum_congr rfl fun j _ => (hsym _ _).symm
  · rintro ⟨P, ⟨hP0, hPs⟩, hc⟩
    refine ⟨fun j => φ (P j), ⟨by
      show φ (P 0) = φ x₀
      rw [hP0], ?_⟩, ?_⟩
    · intro j hne
      have hj : ((j : ℕ)) < σ.length := by
        have h0 := j.isLt
        omega
      have hget : (mapReqs φ σ).get j = φ '' (σ.get ⟨(j : ℕ), hj⟩) := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp [mapReqs, List.getElem_map]
      have hne' : (σ.get ⟨(j : ℕ), hj⟩).Nonempty := by
        by_contra hcon
        rw [Set.not_nonempty_iff_eq_empty] at hcon
        rw [hget, hcon] at hne
        simp at hne
      have h1 := hPs ⟨(j : ℕ), hj⟩ hne'
      rw [hget]
      exact ⟨P ((j : ℕ) + 1), h1, rfl⟩
    · rw [hc, hlen]
      exact Finset.sum_congr rfl fun j _ => (hφ _ _).symm

/-- **Transport of chunk systems along marked bijective isometries.** -/
theorem transport {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b) :
    Nonempty (ChunkSystemB Y (φ s) (φ t) cLo cHi total price mLo) := by
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := C.m
    hist := C.hist
    chunk := fun ω i => mapReqs φ (C.chunk ω i)
    size := C.size
    hP := C.hP
    hPsum := C.hPsum
    hm := C.hm
    hm0 := C.hm0
    href := C.href
    hadapt := fun i ω ω' hh => by rw [C.hadapt i ω ω' hh]
    hsmeas := C.hsmeas
    hne := fun ω i S hS => ?_
    hlast := fun ω => ?_
    hopt := fun ω => ?_
    hsize := C.hsize
    hcost := fun i ω₀ E bail => ?_
    htotal := C.htotal }⟩
  · -- nonemptiness of image sets
    unfold mapReqs at hS
    rw [List.mem_map] at hS
    obtain ⟨S₀, hS₀, rfl⟩ := hS
    exact (C.hne ω i S₀ hS₀).image φ
  · -- last request
    have hflat : (List.ofFn (fun i => mapReqs φ (C.chunk ω i))).flatten
        = mapReqs φ ((List.ofFn (C.chunk ω)).flatten) := by
      rw [mapReqs_flatten]
      congr 1
      rw [List.map_ofFn]
      rfl
    rw [hflat]
    have h1 := C.hlast ω
    unfold mapReqs
    rw [List.getLast?_map, h1]
    simp

  · -- offline optimum
    have hflat : (List.ofFn (fun i => mapReqs φ (C.chunk ω i))).flatten
        = mapReqs φ ((List.ofFn (C.chunk ω)).flatten) := by
      rw [mapReqs_flatten]
      congr 1
      rw [List.map_ofFn]
      rfl
    rw [hflat, offline_map_eq φ hφ]
    rw [show dist (φ s) (φ t) = dist s t from hφ s t]
    exact C.hopt ω
  · -- conditional cost bound
    have h1 := C.hcost i ω₀ (pullEvader φ hφ E) (fun l => bail (mapReqs φ l))
    refine le_trans h1 (le_of_eq ?_)
    refine Finset.sum_congr rfl fun ω hm => ?_
    congr 1
    rw [pullEvader_bailCost]
    congr 1
    rw [mapReqs_flatten]
    congr 1
    rw [List.map_take]
    congr 1
    rw [List.map_ofFn]
    rfl

end Transport

namespace KServer

/-- Chunk systems transport along marked distance-preserving bijections. -/
theorem chunk_system_transport {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b) :
    Nonempty (ChunkSystemB Y (φ s) (φ t) cLo cHi total price mLo) :=
  Transport.transport C φ hφ

end KServer

theorem solution {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : KServer.ChunkSystemB X s t cLo cHi total price mLo)
    (φ : X ≃ Y) (hφ : ∀ a b : X, dist (φ a) (φ b) = dist a b) :
    Nonempty (KServer.ChunkSystemB Y (φ s) (φ t) cLo cHi total price mLo) :=
  KServer.chunk_system_transport C φ hφ
