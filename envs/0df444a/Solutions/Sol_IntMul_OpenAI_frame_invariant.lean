-- Prove2me | solution 1 for IntMul.OpenAI.frame_invariant
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T13:55:37.226129+00:00
-- url     : https://prove2.me/submissions/f77f5aac-7c1c-4c8c-b608-f4c70b6042b5

import Mathlib

open Finset

namespace FrameAux

variable {Wr Ω R : Type*} [CommRing R] [Fintype Wr] [DecidableEq Wr]

abbrev Fr (Ω R : Type*) [CommRing R] := (Ω → R) ≃ₗ[R] (Ω → R)

abbrev GateT (Wr Ω R : Type*) [CommRing R] := Matrix Wr Wr R × Finset Wr × Fr Ω R

def GateOK (g : GateT Wr Ω R) : Prop :=
  ∀ w w', (w ∉ g.2.1 → g.1 w w' = if w = w' then 1 else 0) ∧
    (w ∈ g.2.1 → w' ∉ g.2.1 → g.1 w w' = 0)

def pstep (st : (Wr → Fr Ω R) × (Wr → Ω → R)) (g : GateT Wr Ω R) :
    (Wr → Fr Ω R) × (Wr → Ω → R) :=
  (fun w => if w ∈ g.2.1 then g.2.2 else st.1 w,
   fun w ω => ∑ w', g.1 w w' *
     (if w' ∈ g.2.1 then g.2.2 ((st.1 w').symm (st.2 w')) else st.2 w') ω)

def lstep (h : Wr → Ω → R) (g : GateT Wr Ω R) : Wr → Ω → R :=
  fun w ω => ∑ w', g.1 w w' * h w' ω

lemma step_inv (st : (Wr → Fr Ω R) × (Wr → Ω → R)) (h : Wr → Ω → R)
    (hst : ∀ w, st.2 w = st.1 w (h w)) (g : GateT Wr Ω R) (hg : GateOK g) :
    ∀ w, (pstep st g).2 w = (pstep st g).1 w (lstep h g w) := by
  intro w
  have hmv : ∀ w', (if w' ∈ g.2.1 then g.2.2 ((st.1 w').symm (st.2 w')) else st.2 w') =
      (if w' ∈ g.2.1 then g.2.2 (h w') else st.1 w' (h w')) := by
    intro w'; split_ifs <;> simp [hst w']
  simp only [pstep, lstep, hmv]
  by_cases hw : w ∈ g.2.1
  · simp only [hw, if_true]
    -- the touched row only reads touched wires
    have hsum : (fun ω => ∑ w', g.1 w w' *
        (if w' ∈ g.2.1 then g.2.2 (h w') else st.1 w' (h w')) ω) =
        fun ω => ∑ w', g.1 w w' * (g.2.2 (h w')) ω := by
      funext ω
      refine Finset.sum_congr rfl fun w' _ => ?_
      by_cases hw' : w' ∈ g.2.1
      · simp [hw']
      · simp [hw', (hg w w').2 hw hw']
    rw [hsum]
    have hlin : lstep h g w = ∑ w', g.1 w w' • h w' := by
      funext ω; simp [lstep, Finset.sum_apply, smul_eq_mul]
    rw [hlin, map_sum]
    funext ω
    simp [Finset.sum_apply, map_smul, smul_eq_mul]
  · simp only [hw, if_false]
    have hrow : ∀ b, w ∉ g.2.1 → g.1 w b = if w = b then 1 else 0 := fun b => (hg w b).1
    have hl : lstep h g w = h w := by
      funext ω
      unfold lstep
      rw [Finset.sum_eq_single w]
      · simp [hrow w hw]
      · intro b _ hb; simp [hrow b hw, Ne.symm hb]
      · simp
    rw [hl]
    funext ω
    rw [Finset.sum_eq_single w]
    · simp [hrow w hw, hw]
    · intro b _ hb; simp [hrow b hw, Ne.symm hb]
    · simp

lemma run_inv (gates : List (GateT Wr Ω R)) (hg : ∀ g ∈ gates, GateOK g) :
    ∀ (st : (Wr → Fr Ω R) × (Wr → Ω → R)) (h : Wr → Ω → R),
      (∀ w, st.2 w = st.1 w (h w)) →
      ∀ w, (gates.foldl pstep st).2 w = (gates.foldl pstep st).1 w (gates.foldl lstep h w) := by
  induction gates with
  | nil => intro st h hst; simpa using hst
  | cons g gs ih =>
    intro st h hst
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _
      (step_inv st h hst g (hg g List.mem_cons_self))

end FrameAux

open FrameAux in
theorem solution {Wr Ω R : Type*} [CommRing R] [Fintype Wr] [DecidableEq Wr]
    (gates : List (Matrix Wr Wr R × Finset Wr × ((Ω → R) ≃ₗ[R] (Ω → R))))
    (hgates : ∀ g ∈ gates, ∀ w w', (w ∉ g.2.1 → g.1 w w' = if w = w' then 1 else 0) ∧
      (w ∈ g.2.1 → w' ∉ g.2.1 → g.1 w w' = 0))
    (Din Dout : Wr → ((Ω → R) ≃ₗ[R] (Ω → R))) (f : Wr → Ω → R) :
    let physical := gates.foldl
      (fun (st : (Wr → ((Ω → R) ≃ₗ[R] (Ω → R))) × (Wr → Ω → R)) g =>
        (fun w => if w ∈ g.2.1 then g.2.2 else st.1 w,
         fun w ω => ∑ w', g.1 w w' *
           (if w' ∈ g.2.1 then g.2.2 ((st.1 w').symm (st.2 w')) else st.2 w') ω))
      (Din, f)
    let logical := gates.foldl (fun (h : Wr → Ω → R) g => fun w ω => ∑ w', g.1 w w' * h w' ω)
      (fun w => (Din w).symm (f w))
    ∀ w, Dout w ((physical.1 w).symm (physical.2 w)) = Dout w (logical w) := by
  intro physical logical w
  have := run_inv gates hgates (Din, f) (fun w => (Din w).symm (f w)) (fun w => by simp) w
  change Dout w (((gates.foldl pstep (Din, f)).1 w).symm ((gates.foldl pstep (Din, f)).2 w)) = _
  rw [this]
  simp [logical, lstep]
  rfl
