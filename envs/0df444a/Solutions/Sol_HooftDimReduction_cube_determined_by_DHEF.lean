-- Prove2me | solution 1 for HooftDimReduction.cube_determined_by_DHEF
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:02:15.774996+00:00
-- url     : https://prove2.me/submissions/06834007-a752-454b-af90-a783001951e2

import Mathlib
import Definitions.Def_HooftDimReduction_Defs

open HooftDimReduction in
theorem hooft3cc1_uniq {p : ℕ} {g : (Fin 4 → ZMod p) → ZMod p} (hg : IsPlaquetteRule g)
    (i : Fin 4) (v w : Fin 4 → ZMod p) (h : ∀ j, j ≠ i → v j = w j)
    (hv : g v = 0) (hw : g w = 0) : v i = w i := by
  obtain ⟨a, _, huniq⟩ := hg i v
  have h1 : v i = a := huniq _ (by show g (Function.update v i (v i)) = 0; rw [Function.update_eq_self]; exact hv)
  have h2 : w i = a := by
    apply huniq
    show g (Function.update v i (w i)) = 0
    have : Function.update v i (w i) = w := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact h j hj
    rw [this]; exact hw
  rw [h1, h2]

open HooftDimReduction in
theorem solution (p : ℕ) (g : Fin 6 → (Fin 4 → ZMod p) → ZMod p)
    (hg : ∀ k, IsPlaquetteRule (g k)) (x : Site) (f f' : Site → ZMod p)
    (hf : ∀ k, g k (fun i => f (plaquette (cubeFace x k).1 (cubeFace x k).2 i)) = 0)
    (hf' : ∀ k, g k (fun i => f' (plaquette (cubeFace x k).1 (cubeFace x k).2 i)) = 0)
    (hD : f (x + e2) = f' (x + e2)) (hH : f (x + e2 + e3) = f' (x + e2 + e3))
    (hE : f (x + e3) = f' (x + e3)) (hF : f (x + e1 + e3) = f' (x + e1 + e3)) :
    ∀ a b c : Fin 2,
      f (x + (((a : ℕ) : ℤ), ((b : ℕ) : ℤ), ((c : ℕ) : ℤ))) =
        f' (x + (((a : ℕ) : ℤ), ((b : ℕ) : ℤ), ((c : ℕ) : ℤ))) := by
  -- face (e) ADHE determines A
  have hA : f x = f' x := by
    have h := hooft3cc1_uniq (hg 4) 0 (fun i => f (plaquette x .p23 i))
      (fun i => f' (plaquette x .p23 i)) (by
        intro j hj
        fin_cases j
        · exact absurd rfl hj
        · exact hD
        · exact hH
        · exact hE) (hf 4) (hf' 4)
    exact h
  -- face (c) ABFE determines B
  have hB : f (x + e1) = f' (x + e1) := by
    have h := hooft3cc1_uniq (hg 2) 1 (fun i => f (plaquette x .p13 i))
      (fun i => f' (plaquette x .p13 i)) (by
        intro j hj
        fin_cases j
        · exact hA
        · exact absurd rfl hj
        · exact hF
        · exact hE) (hf 2) (hf' 2)
    exact h
  -- face (a) ABCD determines C
  have hC : f (x + e1 + e2) = f' (x + e1 + e2) := by
    have h := hooft3cc1_uniq (hg 0) 2 (fun i => f (plaquette x .p12 i))
      (fun i => f' (plaquette x .p12 i)) (by
        intro j hj
        fin_cases j
        · exact hA
        · exact hB
        · exact absurd rfl hj
        · exact hD) (hf 0) (hf' 0)
    exact h
  -- face (b) EFGH determines G
  have hF2 : f (x + e3 + e1) = f' (x + e3 + e1) := by
    rw [add_right_comm]; exact hF
  have hH2 : f (x + e3 + e2) = f' (x + e3 + e2) := by
    rw [add_right_comm]; exact hH
  have hG : f (x + e3 + e1 + e2) = f' (x + e3 + e1 + e2) := by
    have h := hooft3cc1_uniq (hg 1) 2 (fun i => f (plaquette (x + e3) .p12 i))
      (fun i => f' (plaquette (x + e3) .p12 i)) (by
        intro j hj
        fin_cases j
        · exact hE
        · exact hF2
        · exact absurd rfl hj
        · exact hH2) (hf 1) (hf' 1)
    exact h
  clear hf hf' hF2 hH2
  have pt : ∀ (a b c : ℤ) (y : Site), y = x + (a, b, c) →
      f y = f' y → f (x + (a, b, c)) = f' (x + (a, b, c)) := by
    intro a b c y hy h; rw [← hy]; exact h
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exact pt _ _ _ x (by ext <;> simp) hA
  · exact pt _ _ _ _ (by ext <;> simp [e3]) hE
  · exact pt _ _ _ _ (by ext <;> simp [e2]) hD
  · exact pt _ _ _ _ (by ext <;> simp [e2, e3]) hH
  · exact pt _ _ _ _ (by ext <;> simp [e1]) hB
  · exact pt _ _ _ _ (by ext <;> simp [e1, e3]) hF
  · exact pt _ _ _ _ (by ext <;> simp [e1, e2]) hC
  · exact pt _ _ _ _ (by ext <;> simp [e1, e2, e3]) hG
