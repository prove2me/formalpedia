-- Prove2me | solution 1 for GreenTao.cs_endpoint_identities
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:55:07.324292+00:00
-- url     : https://prove2.me/submissions/e31a9a0e-22ee-4723-bbac-8b039f713fc7

import Theorems.Thm_GreenTao_cs_coefficients
import Mathlib

open scoped BigOperators
open GreenTao

private lemma avg_const_endpoint {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α => c) = c := by simp [avg, Fintype.card_ne_zero]

private lemma avg_equiv_endpoint {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e _

private lemma avg_comm_endpoint {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    avg (fun a => avg (f a)) = avg (fun b => avg fun a => f a b) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

private lemma avg_surjective_hom {α β : Type} [Fintype α] [Fintype β]
    [AddCommGroup α] [AddCommGroup β] (f : α →+ β) (hf : Function.Surjective f) (g : β → ℝ) :
    avg (fun x => g (f x)) = avg g := by
  have htrans (y : β) : avg (fun x => g (f x + y)) = avg (fun x => g (f x)) := by
    obtain ⟨a, rfl⟩ := hf y
    have h := avg_equiv_endpoint (Equiv.addRight a) (fun x => g (f x))
    change (avg fun x => g (f (x + a))) = _ at h
    simpa only [map_add] using h
  have hinner (x : α) : avg (fun y => g (f x + y)) = avg g :=
    avg_equiv_endpoint (Equiv.addLeft (f x)) g
  calc
    _ = avg (fun y => avg fun x => g (f x + y)) := by simp_rw [htrans, avg_const_endpoint]
    _ = avg (fun x => avg fun y => g (f x + y)) := (avg_comm_endpoint _).symm
    _ = _ := by simp_rw [hinner, avg_const_endpoint]

private lemma ratCoeff_fraction_endpoint (m : ℕ+) [Fact (Nat.Prime (m : ℕ))]
    (a b : ℤ) (hb : (b : ZMod (m : ℕ)) ≠ 0) :
    ratCoeff m ((a : ℚ) / b) = (a : ZMod (m : ℕ)) * (b : ZMod (m : ℕ))⁻¹ := by
  have hb₀ : b ≠ 0 := by intro h; subst b; simpa using hb
  obtain ⟨c, ha, hc⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb₀
  have ha' : (a : ZMod (m : ℕ)) = (c : ZMod (m : ℕ)) * (((a : ℚ) / b).num : ZMod (m : ℕ)) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod (m : ℕ))) ha
  have hb' : (b : ZMod (m : ℕ)) = (c : ZMod (m : ℕ)) * (((a : ℚ) / b).den : ZMod (m : ℕ)) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod (m : ℕ))) hc
  have hp : (c : ZMod (m : ℕ)) * (((a : ℚ) / b).den : ZMod (m : ℕ)) ≠ 0 := by rw [← hb']; exact hb
  have hc' := (mul_ne_zero_iff.mp hp).1
  have hd' := (mul_ne_zero_iff.mp hp).2
  unfold ratCoeff
  rw [ha', hb']
  field_simp
  <;> ring

private lemma natCast_injective_below (m : ℕ+) (a b : ℕ) (ha : a < (m : ℕ)) (hb : b < (m : ℕ))
    (h : (a : ZMod (m : ℕ)) = (b : ZMod (m : ℕ))) : a = b := by
  have hh := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hh

private lemma csCoeff_mod_nonzero (d : ℕ) (m : ℕ+) (hdm : d < (m : ℕ))
    (j : Fin (d + 1)) (i : Fin d) : (csCoeff d j i : ZMod (m : ℕ)) ≠ 0 := by
  intro h
  have heq : ((j.succAbove i).val : ZMod (m : ℕ)) = (j.val : ZMod (m : ℕ)) := by
    simpa only [csCoeff, Int.cast_sub, Int.cast_natCast, sub_eq_zero] using h
  apply j.succAbove_ne i
  apply Fin.ext
  exact natCast_injective_below m _ _ (by omega) (by omega) heq

private lemma csCoeff_mod_injective (d : ℕ) (m : ℕ+) (hdm : d < (m : ℕ))
    (j : Fin (d + 1)) : Function.Injective (fun i : Fin d => (csCoeff d j i : ZMod (m : ℕ))) := by
  intro i l h
  have hh := congrArg (fun z : ZMod (m : ℕ) => z + (j.val : ZMod (m : ℕ))) h
  have heq : ((j.succAbove i).val : ZMod (m : ℕ)) = ((j.succAbove l).val : ZMod (m : ℕ)) := by
    simpa [csCoeff] using hh
  apply (Fin.succAbove_right_injective (p := j))
  apply Fin.ext
  exact natCast_injective_below m _ _ (by omega) (by omega) heq

private lemma csRatCoeff_mod (d : ℕ) (m : ℕ+) [Fact (Nat.Prime (m : ℕ))] (hdm : d < (m : ℕ))
    (j : Fin (d + 1)) (i l : Fin d) :
    ratCoeff m (csRatCoeff d j i l) =
      1 - (csCoeff d j i : ZMod (m : ℕ)) * (csCoeff d j l : ZMod (m : ℕ))⁻¹ := by
  have hcl : csCoeff d j l ≠ 0 := (cs_coefficients d j).1 l |>.1
  have hclq : (csCoeff d j l : ℚ) ≠ 0 := by exact_mod_cast hcl
  have hfrac : csRatCoeff d j i l = ((csCoeff d j l - csCoeff d j i : ℤ) : ℚ) / (csCoeff d j l : ℚ) := by
    dsimp [csRatCoeff]
    push_cast
    field_simp
  rw [hfrac, ratCoeff_fraction_endpoint m _ _ (csCoeff_mod_nonzero d m hdm j l), Int.cast_sub, sub_mul]
  rw [mul_inv_cancel₀ (csCoeff_mod_nonzero d m hdm j l)]

private lemma csForm_reparameterize (d : ℕ) (m : ℕ+) [Fact (Nat.Prime (m : ℕ))] (hdm : d < (m : ℕ))
    (j : Fin (d + 1)) (i : Fin d) (y : Fin d → ZMod (m : ℕ)) :
    csForm d j i y = (∑ a, y a) + (csCoeff d j i : ZMod (m : ℕ)) *
      (-(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a)) := by
  unfold csForm
  simp_rw [csRatCoeff_mod d m hdm, sub_mul, one_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private noncomputable def csCover (d : ℕ) (m : ℕ+) (j : Fin (d + 1)) :
    (Fin d → ZMod (m : ℕ)) →+ (ZMod (m : ℕ) × ZMod (m : ℕ)) where
  toFun y := (∑ a, y a, -(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a))
  map_zero' := by simp
  map_add' := by intro y z; ext <;> simp [mul_add, Finset.sum_add_distrib, add_comm]

private lemma csCover_surjective (d : ℕ) (hd : 2 ≤ d) (m : ℕ+)
    [Fact (Nat.Prime (m : ℕ))] (hdm : d < (m : ℕ)) (j : Fin (d + 1)) :
    Function.Surjective (csCover d m j) := by
  classical
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have hh := congrArg Fin.val h; dsimp [a, b] at hh; omega
  let A : ZMod (m : ℕ) := (csCoeff d j a : ZMod (m : ℕ))⁻¹
  let B : ZMod (m : ℕ) := (csCoeff d j b : ZMod (m : ℕ))⁻¹
  have hAB : A ≠ B := by
    intro h
    apply hab
    apply csCoeff_mod_injective d m hdm j
    simpa only [A, B, inv_inv] using congrArg Inv.inv h
  have hdelta : A - B ≠ 0 := sub_ne_zero.mpr hAB
  rintro ⟨x, r⟩
  let t : ZMod (m : ℕ) := (-(r + B * x)) * (A - B)⁻¹
  let y : Fin d → ZMod (m : ℕ) := fun i =>
    (if i = a then t else 0) + if i = b then x - t else 0
  have hy₀ : (∑ i, y i) = x := by simp [y, Finset.sum_add_distrib]
  have hsum : (∑ i : Fin d, (csCoeff d j i : ZMod (m : ℕ))⁻¹ * y i) = A * t + B * (x - t) := by
    dsimp [y]
    simp_rw [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  have ht : (A - B) * t = -(r + B * x) := by
    dsimp only [t]
    rw [mul_left_comm, mul_inv_cancel₀ hdelta, mul_one]
  have hy₁ : -(∑ i : Fin d, (csCoeff d j i : ZMod (m : ℕ))⁻¹ * y i) = r := by
    rw [hsum]
    linear_combination -ht
  refine ⟨y, ?_⟩
  apply Prod.ext
  · exact hy₀
  · exact hy₁

private lemma avg_prod_endpoint {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg fun b => f (a, b)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

private lemma csCover_average (d : ℕ) (hd : 2 ≤ d) (m : ℕ+)
    [Fact (Nat.Prime (m : ℕ))] (hdm : d < (m : ℕ)) (j : Fin (d + 1))
    (f : ZMod (m : ℕ) × ZMod (m : ℕ) → ℝ) :
    avg (fun y : Fin d → ZMod (m : ℕ) =>
      f (∑ a, y a, -(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a))) =
      avg (fun x => avg fun r => f (x, r)) := by
  calc
    _ = avg f := avg_surjective_hom (csCover d m j) (csCover_surjective d hd m hdm j) f
    _ = _ := avg_prod_endpoint f

private lemma cs_initial_identity (d : ℕ) (hd : 2 ≤ d) (m : ℕ+) (hm : Nat.Prime (m : ℕ))
    (hdm : d < (m : ℕ)) (μ : ZMod (m : ℕ) → ℝ) (j : Fin (d + 1))
    (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) :
    csStage d j μ F 0 = mixedAPAvg (d + 1) F := by
  classical
  letI : Fact (Nat.Prime (m : ℕ)) := ⟨hm⟩
  have htail : csTail d 0 = ∅ := by ext a; simp only [csTail, Nat.sub_zero,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
  have hpoint (y y' : Fin d → ZMod (m : ℕ)) (ω : (∅ : Finset (Fin d)) → Bool) :
      partialCubePoint ∅ y y' ω = y := by funext a; simp [partialCubePoint]
  have hstart : csStage d j μ F 0 = avg (fun y : Fin d → ZMod (m : ℕ) =>
      F j (∑ a, y a) * ∏ i : Fin d, F (j.succAbove i) (csForm d j i y)) := by
    unfold csStage
    rw [htail]
    simp_rw [hpoint]
    simp [avg_const_endpoint]
  let T : ZMod (m : ℕ) × ZMod (m : ℕ) → ℝ := fun p =>
    F j p.1 * ∏ i : Fin d, F (j.succAbove i) (p.1 + (csCoeff d j i : ZMod (m : ℕ)) * p.2)
  have hp (x r : ZMod (m : ℕ)) : T (x, r) =
      ∏ a : Fin (d + 1), F a (x + ((a.val : ZMod (m : ℕ)) - (j.val : ZMod (m : ℕ))) * r) := by
    dsimp [T]
    rw [Fin.prod_univ_succAbove _ j]
    simp only [sub_self, zero_mul, add_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    simp [csCoeff]
  have hshift (r : ZMod (m : ℕ)) :
      (avg fun x => ∏ a : Fin (d + 1), F a (x + ((a.val : ZMod (m : ℕ)) - (j.val : ZMod (m : ℕ))) * r)) =
      avg (fun x => ∏ a : Fin (d + 1), F a (x + (a.val : ZMod (m : ℕ)) * r)) := by
    let z : ZMod (m : ℕ) := -(j.val : ZMod (m : ℕ)) * r
    calc
      _ = avg (fun x => ∏ a : Fin (d + 1), F a ((x + z) + (a.val : ZMod (m : ℕ)) * r)) := by
        congr 1
        funext x
        apply Finset.prod_congr rfl
        intro a _
        congr 1
        dsimp [z]
        ring
      _ = _ := avg_equiv_endpoint (Equiv.addRight z)
        (fun x => ∏ a : Fin (d + 1), F a (x + (a.val : ZMod (m : ℕ)) * r))
  calc
    _ = avg (fun y : Fin d → ZMod (m : ℕ) =>
        T (∑ a, y a, -(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a))) := by
      rw [hstart]
      simp_rw [csForm_reparameterize d m hdm]
      rfl
    _ = avg (fun x => avg fun r => T (x, r)) := csCover_average d hd m hdm j T
    _ = _ := by
      simp_rw [hp]
      rw [avg_comm_endpoint]
      simp_rw [hshift]
      exact (avg_comm_endpoint (fun x r => ∏ a : Fin (d + 1),
        F a (x + (a.val : ZMod (m : ℕ)) * r))).symm

private lemma sqrt_cube_faces (d : ℕ) (i : Fin d) (g : (Fin d → Bool) → ℝ)
    (hg : ∀ ω, 0 ≤ g ω) (hi : ∀ ω, g (Function.update ω i false) = g ω) :
    (∏ ω : Fin d → Bool, Real.sqrt (g ω)) =
      ∏ ω : Fin d → Bool with ω i = false, g ω := by
  classical
  let e : (Fin d → Bool) ≃ Bool × ({a : Fin d // a ≠ i} → Bool) := Equiv.funSplitAt i Bool
  let ef : {ω : Fin d → Bool // ω i = false} ≃ ({a : Fin d // a ≠ i} → Bool) :=
    { toFun := fun ω a => ω.val a.val
      invFun := fun u => ⟨fun a => if ha : a = i then false else u ⟨a, ha⟩, by simp⟩
      left_inv := by
        intro ω
        apply Subtype.ext
        funext a
        by_cases ha : a = i
        · subst a; simp [ω.property]
        · simp [ha]
      right_inv := by intro u; funext a; simp [a.property] }
  have hupdate (u : {a : Fin d // a ≠ i} → Bool) :
      Function.update (e.symm (true, u)) i false = e.symm (false, u) := by
    funext a
    by_cases ha : a = i
    · subst a; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update, ha]
  have heq (u : {a : Fin d // a ≠ i} → Bool) : g (e.symm (true, u)) = g (e.symm (false, u)) := by
    rw [← hi (e.symm (true, u)), hupdate]
  calc
    _ = ∏ p : Bool × ({a : Fin d // a ≠ i} → Bool), Real.sqrt (g (e.symm p)) :=
      (Equiv.prod_comp e.symm (fun ω => Real.sqrt (g ω))).symm
    _ = (∏ u : {a : Fin d // a ≠ i} → Bool, Real.sqrt (g (e.symm (false, u)))) ^ 2 := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool]
      simp_rw [heq]
      ring
    _ = ∏ u : {a : Fin d // a ≠ i} → Bool, g (e.symm (false, u)) := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun u _ => Real.sq_sqrt (hg _)
    _ = ∏ ω : {ω : Fin d → Bool // ω i = false}, g ω.val := by
      have h := Equiv.prod_comp ef.symm (fun ω => g ω.val)
      have hefu (u : {a : Fin d // a ≠ i} → Bool) : e.symm (false, u) = (ef.symm u).val := by
        funext a
        by_cases ha : a = i
        · subst a; simp [e, ef, Equiv.funSplitAt, Equiv.piSplitAt]
        · simp [e, ef, Equiv.funSplitAt, Equiv.piSplitAt, ha]
      simpa only [hefu] using h
    _ = _ := (Finset.prod_subtype (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false))
      (by simp) g).symm

private lemma full_stage_expansion (d : ℕ) (m : ℕ+) (μ : ZMod (m : ℕ) → ℝ)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) :
    csStage d j μ F d = avg (fun y : Fin d → ZMod (m : ℕ) =>
      avg fun y' : Fin d → ZMod (m : ℕ) => ∏ ω : Fin d → Bool,
        F j (∑ a, if ω a then y' a else y a) *
          ∏ i : Fin d, Real.sqrt (μ (csForm d j i (fun a => if ω a then y' a else y a)))) := by
  classical
  have htail : csTail d d = Finset.univ := by simp [csTail]
  let e : (Fin d → Bool) ≃ (↥(Finset.univ : Finset (Fin d)) → Bool) :=
    { toFun := fun ω a => ω a.val
      invFun := fun ω a => ω ⟨a, Finset.mem_univ a⟩
      left_inv := by intro ω; rfl
      right_inv := by intro ω; funext a; rfl }
  have hp (y y' : Fin d → ZMod (m : ℕ)) (ω : Fin d → Bool) :
      partialCubePoint Finset.univ y y' (e ω) = (fun a => if ω a then y' a else y a) := by
    funext a
    simp [partialCubePoint, e]
  unfold csStage
  rw [htail]
  simp only [Finset.mem_univ, if_true]
  congr 1
  funext y
  congr 1
  funext y'
  have h := Equiv.prod_comp e (fun ω => F j (∑ a, partialCubePoint Finset.univ y y' ω a) *
    ∏ i : Fin d, Real.sqrt (μ (csForm d j i (partialCubePoint Finset.univ y y' ω))))
  simpa only [hp] using h.symm

private lemma weighted_face_invariance (d : ℕ) (m : ℕ+) (μ : ZMod (m : ℕ) → ℝ)
    (j : Fin (d + 1)) (i : Fin d) (x r : ZMod (m : ℕ)) (h : Fin d → ZMod (m : ℕ))
    (ω : Fin d → Bool) :
    μ (x + (csCoeff d j i : ZMod (m : ℕ)) * r +
      ∑ a : Fin d, ratCoeff m (csRatCoeff d j i a) * (if Function.update ω i false a then h a else 0)) =
    μ (x + (csCoeff d j i : ZMod (m : ℕ)) * r +
      ∑ a : Fin d, ratCoeff m (csRatCoeff d j i a) * (if ω a then h a else 0)) := by
  have hdiag : csRatCoeff d j i i = 0 := (cs_coefficients d j).2.2.2 i i |>.2 rfl
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases hai : a = i
  · subst a; simp [hdiag, ratCoeff]
  · simp [Function.update, hai]

private lemma csForm_add_cube (d : ℕ) (m : ℕ+) (j : Fin (d + 1)) (i : Fin d)
    (y h : Fin d → ZMod (m : ℕ)) (ω : Fin d → Bool) :
    csForm d j i (fun a => y a + if ω a then h a else 0) =
      csForm d j i y + ∑ a : Fin d, ratCoeff m (csRatCoeff d j i a) * (if ω a then h a else 0) := by
  simp [csForm, mul_add, Finset.sum_add_distrib]

set_option maxHeartbeats 1000000 in
private lemma cs_terminal_identity (d : ℕ) (hd : 2 ≤ d) (m : ℕ+) (hm : Nat.Prime (m : ℕ))
    (hdm : d < (m : ℕ)) (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) :
    csStage d j μ F d = weightedCubeAvg d (csWeight d j μ) (F j) := by
  classical
  letI : Fact (Nat.Prime (m : ℕ)) := ⟨hm⟩
  let V (x : ZMod (m : ℕ)) (h : Fin d → ZMod (m : ℕ)) : ℝ :=
    ∏ ω : Fin d → Bool, F j (x + ∑ a : Fin d, if ω a then h a else 0)
  let B (x : ZMod (m : ℕ)) (h : Fin d → ZMod (m : ℕ)) (r : ZMod (m : ℕ)) : ℝ :=
    ∏ i : Fin d, ∏ ω : Fin d → Bool with ω i = false,
      μ (x + (csCoeff d j i : ZMod (m : ℕ)) * r +
        ∑ a : Fin d, ratCoeff m (csRatCoeff d j i a) * (if ω a then h a else 0))
  let K : (Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ)) → ℝ := fun p =>
    ∏ ω : Fin d → Bool, F j (∑ a, if ω a then p.2 a else p.1 a) *
      ∏ i : Fin d, Real.sqrt (μ (csForm d j i (fun a => if ω a then p.2 a else p.1 a)))
  let e : ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) ≃
      ((Fin d → ZMod (m : ℕ)) × (Fin d → ZMod (m : ℕ))) :=
    { toFun := fun p => (p.1, p.1 + p.2)
      invFun := fun p => (p.1, p.2 - p.1)
      left_inv := by intro p; ext a <;> simp
      right_inv := by intro p; ext a <;> simp }
  have hp (y h : Fin d → ZMod (m : ℕ)) : K (e (y, h)) =
      V (∑ a, y a) h * B (∑ a, y a) h (-(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a)) := by
    have hbit (ω : Fin d → Bool) (a : Fin d) :
        (if ω a then y a + h a else y a) = y a + if ω a then h a else 0 := by cases ω a <;> simp
    dsimp [K, e, V, B]
    simp_rw [hbit, Finset.sum_add_distrib, csForm_add_cube,
      csForm_reparameterize d m hdm, Finset.prod_mul_distrib]
    rw [Finset.prod_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact sqrt_cube_faces d i _ (fun ω => hμ _)
      (fun ω => weighted_face_invariance d m μ j i (∑ a, y a)
        (-(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a)) h ω)
  calc
    csStage d j μ F d = avg K := by
      rw [full_stage_expansion]
      exact (avg_prod_endpoint K).symm
    _ = avg (fun p => K (e p)) := (avg_equiv_endpoint e K).symm
    _ = avg (fun y : Fin d → ZMod (m : ℕ) => avg fun h : Fin d → ZMod (m : ℕ) => V (∑ a, y a) h *
        B (∑ a, y a) h (-(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a))) := by
      rw [avg_prod_endpoint]
      simp_rw [hp]
    _ = avg (fun h : Fin d → ZMod (m : ℕ) => avg fun y : Fin d → ZMod (m : ℕ) => V (∑ a, y a) h *
        B (∑ a, y a) h (-(∑ a : Fin d, (csCoeff d j a : ZMod (m : ℕ))⁻¹ * y a))) := avg_comm_endpoint _
    _ = avg (fun h : Fin d → ZMod (m : ℕ) => avg fun x : ZMod (m : ℕ) => avg fun r : ZMod (m : ℕ) => V x h * B x h r) := by
      congr 1
      funext h
      exact csCover_average d hd m hdm j (fun p => V p.1 h * B p.1 h p.2)
    _ = avg (fun x : ZMod (m : ℕ) => avg fun h : Fin d → ZMod (m : ℕ) => avg fun r : ZMod (m : ℕ) => V x h * B x h r) := (avg_comm_endpoint _).symm
    _ = _ := by
      unfold weightedCubeAvg
      congr 1
      funext x
      congr 1
      funext h
      have hh : avg (fun r : ZMod (m : ℕ) => V x h * B x h r) = V x h * avg (B x h) := by
        simp only [avg, ← Finset.mul_sum]
        ring
      rw [hh]
      change V x h * csWeight d j μ x h = csWeight d j μ x h * V x h
      ring

theorem solution
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ+) (hm : Nat.Prime (m : ℕ)) (hdm : d < (m : ℕ))
    (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) :
    GreenTao.csStage d j μ F 0 = GreenTao.mixedAPAvg (d + 1) F ∧
      GreenTao.csStage d j μ F d =
        GreenTao.weightedCubeAvg d (GreenTao.csWeight d j μ) (F j) := by
  exact ⟨cs_initial_identity d hd m hm hdm μ j F, cs_terminal_identity d hd m hm hdm μ hμ j F⟩
