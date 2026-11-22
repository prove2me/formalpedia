-- Prove2me | solution 1 for Monotonicity_Theorem.locally_constant_implies_constant
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T20:50:35.96399+00:00
-- url     : https://prove2.me/submissions/0f5eea74-3618-4260-ad7d-7c3664c56061

import Theorems.Thm_Monotonicity_Theorem_definable_preimage
import Theorems.Thm_Monotonicity_Theorem_definable_interval_dichotomy
import Definitions.Def_Monotonicity_Theorem_Window_Loci

set_option autoImplicit false

open Monotonicity_Theorem

namespace LGAux

variable {R : Type}

lemma power1_ext {a b : Power R 1} (h : a 0 = b 0) : a = b := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  exact h

/-- The point of the line with coordinate `t`. -/
def ptOf (t : R) : Power R 1 := fun _ => t

/-- Propagation of a definable property along an interval.

`A` is a definable set, `F` its finite exceptional set given by the interval dichotomy, and `L`
a list of the coordinates of `F`.  Assuming that from any starting point one can find a point of
`A` immediately to the right (`hW`) and that a point of `A` immediately to the left of `y`
forces `y ∈ A` (`hE`), every point of the interval to the right of a starting point is in `A`. -/
lemma chain_propagation (D : DenseLinearOrderNoEndpoints R) (u v : R)
    (A : Set (Power R 1)) (Start : Power R 1 → Prop)
    (F : Set (Power R 1)) (L : List R) (hL : ∀ z : Power R 1, F z ↔ z 0 ∈ L)
    (hdich : ∀ a b : R, D.lt a b →
      (∀ z : Power R 1, openInterval D (Endpoint.finite a) (Endpoint.finite b) z → ¬ F z) →
      ((openInterval D (Endpoint.finite a) (Endpoint.finite b)).Subset A ∨
        ∀ z : Power R 1, openInterval D (Endpoint.finite a) (Endpoint.finite b) z → ¬ A z))
    (hAstart : ∀ z, A z → Start z)
    (hW : ∀ x' y' : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → Start x' → ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t))
    (hE : ∀ y' : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
        D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y') :
    ∀ (l : List R) (x' y' : Power R 1),
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
      D.lt (x' 0) (y' 0) → Start x' →
      (∀ w ∈ L, D.lt (x' 0) w → D.lt w (y' 0) → w ∈ l) → A y' := by
  intro l
  induction l with
  | nil =>
      intro x' y' hx' hy' hlt hstart hcov
      -- no exceptional point lies strictly between `x'` and `y'`
      have havoid : ∀ z : Power R 1,
          openInterval D (Endpoint.finite (x' 0)) (Endpoint.finite (y' 0)) z → ¬ F z := by
        intro z hz hFz
        have := hcov (z 0) ((hL z).1 hFz) hz.1 hz.2
        simp at this
      have hsubA : (openInterval D (Endpoint.finite (x' 0)) (Endpoint.finite (y' 0))).Subset A := by
        rcases hdich (x' 0) (y' 0) hlt havoid with h | h
        · exact h
        · obtain ⟨t, ht₁, ht₂, hAt⟩ := hW x' y' hx' hy' hlt hstart
          exact absurd hAt (h (ptOf t) ⟨ht₁, ht₂⟩)
      -- every point strictly between lies in the ambient interval
      have hbetween : ∀ z : Power R 1,
          openInterval D (Endpoint.finite (x' 0)) (Endpoint.finite (y' 0)) z →
          openInterval D (Endpoint.finite u) (Endpoint.finite v) z :=
        fun z hz => ⟨D.trans hx'.1 hz.1, D.trans hz.2 hy'.2⟩
      obtain ⟨a, ha, hEa⟩ := hE y' hy'
      -- choose a point of `A` between `max a (x' 0)` and `y' 0`
      obtain ⟨s, hs₁, hs₂, hs₃⟩ :
          ∃ s : R, D.lt (x' 0) s ∧ D.lt s (y' 0) ∧ D.lt a s := by
        rcases D.trichotomy a (x' 0) with h | h | h
        · obtain ⟨s, hs₁, hs₂⟩ := D.dense hlt
          exact ⟨s, hs₁, hs₂, D.trans h.1 hs₁⟩
        · obtain ⟨s, hs₁, hs₂⟩ := D.dense hlt
          exact ⟨s, hs₁, hs₂, h.1 ▸ hs₁⟩
        · obtain ⟨s, hs₁, hs₂⟩ := D.dense ha
          exact ⟨s, D.trans h.1 hs₁, hs₂, hs₁⟩
      have hsJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf s) :=
        hbetween (ptOf s) ⟨hs₁, hs₂⟩
      exact hEa (ptOf s) hsJ hs₃ hs₂ (hsubA ⟨hs₁, hs₂⟩)
  | cons c l ih =>
      intro x' y' hx' hy' hlt hstart hcov
      by_cases hc : c ∈ L ∧ D.lt (x' 0) c ∧ D.lt c (y' 0)
      · obtain ⟨hcL, hcx, hcy⟩ := hc
        have hcJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf c) :=
          ⟨D.trans hx'.1 hcx, D.trans hcy hy'.2⟩
        by_cases hAc : A (ptOf c)
        · refine ih (ptOf c) y' hcJ hy' hcy (hAstart _ hAc) ?_
          intro w hw hw₁ hw₂
          have hmem := hcov w hw (D.trans hcx hw₁) hw₂
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact absurd hw₁ (D.irrefl w)
          · exact hmem
        · exfalso
          refine hAc (ih x' (ptOf c) hx' hcJ hcx hstart ?_)
          intro w hw hw₁ hw₂
          have hmem := hcov w hw hw₁ (D.trans hw₂ hcy)
          rcases List.mem_cons.1 hmem with rfl | hmem
          · exact absurd hw₂ (D.irrefl w)
          · exact hmem
      · refine ih x' y' hx' hy' hlt hstart ?_
        intro w hw hw₁ hw₂
        have hmem := hcov w hw hw₁ hw₂
        rcases List.mem_cons.1 hmem with rfl | hmem
        · exact absurd ⟨hw, hw₁, hw₂⟩ hc
        · exact hmem

/-- Choose a point strictly between `x` and `min b y`. -/
private lemma exists_between_of_lt (D : DenseLinearOrderNoEndpoints R) {x y b : R}
    (hxy : D.lt x y) (hxb : D.lt x b) :
    ∃ t : R, D.lt x t ∧ D.lt t y ∧ D.lt t b := by
  rcases D.trichotomy b y with h | h | h
  · obtain ⟨t, h1, h2⟩ := D.dense hxb
    exact ⟨t, h1, D.trans h2 h.1, h2⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hxb
    exact ⟨t, h1, h.1 ▸ h2, h2⟩
  · obtain ⟨t, h1, h2⟩ := D.dense hxy
    exact ⟨t, h1, h2, D.trans h2 h.1⟩


end LGAux

open LGAux in
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset
      (ConstWindowLocus f)) :
    ConstOnInterval f u v := by
  have key : ∀ x y : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
      D.lt (x 0) (y 0) → ∀ (hxI : I x) (hyI : I y),
        (f.toFun (Subtype.mk x hxI)).1 0 = (f.toFun (Subtype.mk y hyI)).1 0 := by
    intro x y hxJ hyJ hlt hxI hyI
    set c : R := (f.toFun (Subtype.mk x hxI)).1 0 with hc
    set A : Set (Power R 1) :=
      fun z => ∃ hz : I z, pointSet c ((f.toFun (Subtype.mk z hz)).1) with hAdef
    have hA : M.S 1 A :=
      definable_preimage D M f ((M.ominimal _).2 (FiniteUnionOfPointsAndIntervals.point c))
    obtain ⟨F, hFfin, hdich⟩ := definable_interval_dichotomy D ((M.ominimal A).1 hA)
    obtain ⟨L, hL⟩ := hFfin
    have hW : ∀ x' y' : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) x' →
        openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
        D.lt (x' 0) (y' 0) → (x' = x ∨ A x') →
        ∃ t : R, D.lt (x' 0) t ∧ D.lt t (y' 0) ∧ A (ptOf t) := by
      intro x' y' hx'J hy'J hlt' hstart
      obtain ⟨a, b, ha, hb, hconst⟩ := hloc hx'J
      obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_between_of_lt D hlt' hb
      have htJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (ptOf t) :=
        ⟨D.trans hx'J.1 ht₁, D.trans ht₂ hy'J.2⟩
      have htI : I (ptOf t) := hsub htJ
      have hx'I : I x' := hsub hx'J
      have hval : f.toFun (Subtype.mk (ptOf t) htI) = f.toFun (Subtype.mk x' hx'I) :=
        hconst (ptOf t) htI ⟨D.trans ha ht₁, ht₃⟩ x' hx'I ⟨ha, hb⟩
      refine ⟨t, ht₁, ht₂, htI, ?_⟩
      show (f.toFun (Subtype.mk (ptOf t) htI)).1 0 = c
      rw [hval]
      rcases hstart with rfl | ⟨hz, hzc⟩
      · rfl
      · exact hzc
    have hE : ∀ y' : Power R 1,
        openInterval D (Endpoint.finite u) (Endpoint.finite v) y' →
        ∃ a : R, D.lt a (y' 0) ∧ ∀ s : Power R 1,
          openInterval D (Endpoint.finite u) (Endpoint.finite v) s →
          D.lt a (s 0) → D.lt (s 0) (y' 0) → A s → A y' := by
      intro y' hy'J
      obtain ⟨a, b, ha, hb, hconst⟩ := hloc hy'J
      refine ⟨a, ha, ?_⟩
      intro s hsJ has hsy hAs
      obtain ⟨hsI, hsc⟩ := hAs
      have hy'I : I y' := hsub hy'J
      have hval : f.toFun (Subtype.mk s hsI) = f.toFun (Subtype.mk y' hy'I) :=
        hconst s hsI ⟨has, D.trans hsy hb⟩ y' hy'I ⟨ha, hb⟩
      exact ⟨hy'I, by rw [← hval]; exact hsc⟩
    have hAy : A y :=
      chain_propagation D u v A (fun z => z = x ∨ A z) F L hL hdich
        (fun z hz => Or.inr hz) hW hE L x y hxJ hyJ hlt (Or.inl rfl) (fun w hw _ _ => hw)
    obtain ⟨hz, hzc⟩ := hAy
    exact hzc.symm
  intro x hxI hxJ y hyI hyJ
  rcases D.trichotomy (x 0) (y 0) with h | h | h
  · exact Subtype.ext (power1_ext (key x y hxJ hyJ h.1 hxI hyI))
  · have : x = y := power1_ext h.1
    subst this
    rfl
  · exact Subtype.ext (power1_ext (key y x hyJ hxJ h.1 hyI hxI)).symm

