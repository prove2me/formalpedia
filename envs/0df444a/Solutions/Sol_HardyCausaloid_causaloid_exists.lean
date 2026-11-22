-- Prove2me | solution 1 for HardyCausaloid.causaloid_exists
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:37:55.083793+00:00
-- url     : https://prove2.me/submissions/0e0e127f-dcd6-4207-88ae-bdc99ef6bedd

import Definitions.Def_HardyCausaloid_Causaloid
import Theorems.Thm_HardyCausaloid_product_reconstruction

namespace HardyCausaloid
private theorem shrink_rows {A S : Type*} (q : A → S → ℝ) (Ω : Finset A)
    (hs : Sufficient q Ω) : ∃ B ⊆ Ω, Fiducial q B := by
  classical
  induction Ω using Finset.strongInductionOn with
  | _ Ω ih =>
    by_cases min : ∀ B : Finset A, B ⊂ Ω → ¬ Sufficient q B
    · exact ⟨Ω, Finset.Subset.refl _, hs, min⟩
    · push Not at min
      obtain ⟨B, hB, hS⟩ := min
      obtain ⟨C, hC, hF⟩ := ih B hB hS
      exact ⟨C, hC.trans hB.subset, hF⟩

private theorem compress_grid {A S K : Type*} [Fintype K] (e : K ↪ A) (q : A → S → ℝ)
    (w : A → K → ℝ) (reconstruct : ∀ α s, q α s = ∑ l, w α l * q (e l) s) :
    ∃ (U : Finset K) (Λ : K → U → ℝ), Fiducial q (U.map e) ∧
      ∀ k s, q (e k) s = ∑ j : U, Λ k j * q (e j.val) s := by
  classical
  let Γ := Finset.univ.map e
  let b : K ≃ Γ := Equiv.ofBijective (fun k => ⟨e k, Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => e.injective (congrArg Subtype.val h), by
      rintro ⟨y, hy⟩
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hy
      exact ⟨k, rfl⟩⟩
  have hs : Sufficient q Γ := by
    intro α
    refine ⟨fun z => w α (b.symm z), fun s => ?_⟩
    rw [reconstruct α s, dotProduct, ← b.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rfl
  obtain ⟨B, sub, hB⟩ := shrink_rows q Γ hs
  let U := Finset.univ.filter (fun k => e k ∈ B)
  have image : U.map e = B := by
    ext y
    constructor
    · rintro hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hy
      exact (Finset.mem_filter.mp hk).2
    · intro hy
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp (sub hy)
      exact Finset.mem_map.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
  have fid : Fiducial q (U.map e) := image.symm ▸ hB
  choose r hr using fid.1
  let d := Finset.equivMap e U
  refine ⟨U, fun k j => r (e k) (d j), fid, fun k s => ?_⟩
  exact (hr (e k) s).trans (d.sum_comp (fun y => r (e k) y * stateVec q (U.map e) s y)).symm

variable {X : Type*} {Setting : X → Type*} {Outcome : (x : X) → Setting x → Type*}
  [DecidableEq X]

private theorem glue_update_site {O : Finset X} (α : Lab Setting Outcome O)
    (i : O) (a : Label Setting Outcome i.val) (s : ∀ x, Label Setting Outcome x) :
    glue O (Function.update α i a) s = Function.update (glue O α s) i.val a := by
  funext x
  by_cases h : x = i.val
  · subst x; simp [glue, i.property]
  · by_cases hx : x ∈ O
    · have hn : (⟨x,hx⟩ : O) ≠ i := fun he => h (congrArg Subtype.val he)
      simp [glue, hx, Function.update_of_ne h, Function.update_of_ne hn]
    · simp [glue, hx, Function.update_of_ne h]

theorem _root_.solution (M : Model Setting Outcome)
    (Ω₁ : ∀ x, Finset (Label Setting Outcome x))
    (hΩ₁ : ∀ x, Fiducial (elemTable M x) (Ω₁ x)) :
    ∃ C : Causaloid Setting Outcome, C.Ω₁ = Ω₁ ∧ IsCausaloidOf C M := by
  classical
  choose u hu using fun x a => (hΩ₁ x).1 a
  let w (x : X) (a : Label Setting Outcome x) (j : Ω₁ x) : ℝ :=
    if ha : a ∈ Ω₁ x then (if (⟨a,ha⟩ : Ω₁ x) = j then 1 else 0) else u x a j
  have unit (x) (k j : Ω₁ x) : w x k.val j = if k = j then 1 else 0 := by simp [w, k.property]
  have hw x a s : elemTable M x a s = w x a ⬝ᵥ stateVec (elemTable M x) (Ω₁ x) s := by
    by_cases ha : a ∈ Ω₁ x
    · let k : Ω₁ x := ⟨a, ha⟩
      change elemTable M x k.val s = ∑ j, w x k.val j * elemTable M x j.val s
      simp [unit]
    · simpa [w, ha] using hu x a s
  let emb (O : Finset X) : (∀ x : O, Ω₁ x.val) ↪ Lab Setting Outcome O :=
    ⟨fun l x => (l x).val, fun a b h => funext fun x => Subtype.ext (congrFun h x)⟩
  let weight (O : Finset X) (α : Lab Setting Outcome O) (l : ∀ x : O, Ω₁ x.val) :=
    ∏ x : O, w x.val (α x) (l x)
  have product (O : Finset X) (α : Lab Setting Outcome O) s :
      regionTable M O α s = ∑ l, weight O α l * regionTable M O (emb O l) s := by
    apply product_reconstruction (fun x : O => Ω₁ x.val) (fun x : O => w x.val)
      (fun t => regionTable M O t s) ?_ (fun i k j => by by_cases he : k = j <;> simpa [he] using unit i.val k j) α
    intro t i
    have h := hw i.val (t i) (glue O t s)
    simpa only [elemTable, stateVec, dotProduct, ← glue_update_site, Function.update_eq_self,
      regionTable] using h
  choose U L fid row using fun O => compress_grid (emb O) (regionTable M O) (weight O) (product O)
  let C : Causaloid Setting Outcome := ⟨Ω₁,w,U,L⟩
  refine ⟨C,rfl,⟨hΩ₁, hw, fid, ?_⟩⟩
  intro O α s
  calc
    regionTable M O α s = ∑ l, weight O α l * regionTable M O (emb O l) s := product O α s
    _ = ∑ l, ∑ k : U O, (weight O α l * L O l k) * regionTable M O (emb O k.val) s := by
      apply Finset.sum_congr rfl
      intro l _
      rw [row O l s, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
    _ = C.r O α ⬝ᵥ C.state M O s := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm

end HardyCausaloid
