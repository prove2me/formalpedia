-- Prove2me | solution 1 for OAI.ArtinCAT0.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T11:48:28.065723+00:00
-- url     : https://prove2.me/submissions/2c146701-5237-4f85-b062-edb041170f15

import Mathlib
import Definitions.Def_ArtinCAT0

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe uS uG uX u v

section
section
namespace OAI

namespace ArtinCAT0

end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

section Comparison

variable {X : Type*} [MetricSpace X]

lemma segment_reverse {x y : X} {γ : ℝ → X} (h : Segment x y γ) :
    Segment y x (fun t => γ (1 - t)) := by
  refine ⟨by simpa using h.2.1, by simpa using h.1, ?_⟩
  intro s hs t ht
  rw [h.2.2 (1 - s) (by constructor <;> linarith [hs.1, hs.2])
    (1 - t) (by constructor <;> linarith [ht.1, ht.2])]
  rw [dist_comm y x]
  congr 1
  rw [show (1 - s) - (1 - t) = t - s by ring, abs_sub_comm t s]

lemma segment_isometry {Z : Type*} [MetricSpace Z] {x y : X} {γ : ℝ → X}
    (h : Segment x y γ) {f : X → Z} (hf : Isometry f) :
    Segment (f x) (f y) (f ∘ γ) := by
  refine ⟨congrArg f h.1, congrArg f h.2.1, ?_⟩
  intro s hs t ht
  simpa only [Function.comp_apply, hf.dist_eq] using h.2.2 s hs t ht

lemma comparison_common_start (hX : CAT0 X) {x y z : X} {γ η : ℝ → X}
    (hγ : Segment x y γ) (hη : Segment x z η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    dist (γ t) (η t) ≤ t * dist y z := by
  have hc := hX.2 x y z γ η hγ hη t ht t ht
  have h₀ := dist_nonneg (x := γ t) (y := η t)
  have h₁ := dist_nonneg (x := y) (y := z)
  have h₂ : 0 ≤ t * dist y z := mul_nonneg ht.1 h₁
  nlinarith [sq_nonneg (dist (γ t) (η t) - t * dist y z)]

lemma segment_unique (hX : CAT0 X) {x y : X} {γ η : ℝ → X}
    (hγ : Segment x y γ) (hη : Segment x y η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    γ t = η t := by
  have h := comparison_common_start hX hγ hη ht
  simpa using h

lemma comparison_convexity (hX : CAT0 X) {a b c d : X} {γ η : ℝ → X}
    (hγ : Segment a b γ) (hη : Segment c d η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    dist (γ t) (η t) ≤ (1 - t) * dist a c + t * dist b d := by
  obtain ⟨ζ, hζ⟩ := hX.1 a d
  have h₁ := comparison_common_start hX hγ hζ ht
  have h₂ := comparison_common_start hX (segment_reverse hζ) (segment_reverse hη)
    (show 1 - t ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2])
  simp only [sub_sub_cancel] at h₂
  calc
    dist (γ t) (η t) ≤ dist (γ t) (ζ t) + dist (ζ t) (η t) := dist_triangle _ _ _
    _ ≤ t * dist b d + (1 - t) * dist a c := add_le_add h₁ h₂
    _ = _ := add_comm _ _

lemma midpoint_comparison (hX : CAT0 X) (z : X) {x y : X} {γ : ℝ → X}
    (hγ : Segment x y γ) :
    dist z (γ (1 / 2)) ^ 2 ≤ (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  obtain ⟨η, hη⟩ := hX.1 x z
  have hc := hX.2 x y z γ η hγ hη (1 / 2) (by constructor <;> norm_num)
    1 (by constructor <;> norm_num)
  rw [hη.2.1, dist_comm (γ _), dist_comm x z, dist_comm y z] at hc
  nlinarith

lemma quadrilateral (hX : CAT0 X) (p q r s : X) :
    dist p r ^ 2 + dist q s ^ 2 ≤
      dist p q ^ 2 + dist q r ^ 2 + dist r s ^ 2 + dist s p ^ 2 := by
  obtain ⟨γ, hγ⟩ := hX.1 p r
  have hq := midpoint_comparison hX q hγ
  have hs := midpoint_comparison hX s hγ
  have ht := dist_triangle q (γ (1 / 2)) s
  rw [dist_comm (γ _)] at ht
  rw [dist_comm q p] at hq
  rw [dist_comm s r] at hs
  have hsum : dist q s ^ 2 ≤ (dist q (γ (1 / 2)) + dist s (γ (1 / 2))) ^ 2 := by
    nlinarith [dist_nonneg (x := q) (y := s),
      dist_nonneg (x := q) (y := γ (1 / 2)), dist_nonneg (x := s) (y := γ (1 / 2))]
  nlinarith [sq_nonneg (dist q (γ (1 / 2)) - dist s (γ (1 / 2)))]

end Comparison

section StableLengths

open Filter Topology

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

noncomputable def stableLengthAt (x : X) (g : G) : ℝ :=
  sInf ((fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ)) '' Set.Ici 1)

lemma displacement_subadditive (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : Subadditive (fun n : ℕ => dist x ((g ^ n) • x)) := by
  intro m n
  calc
    dist x ((g ^ (m + n)) • x) ≤
        dist x ((g ^ m) • x) + dist ((g ^ m) • x) ((g ^ m) • ((g ^ n) • x)) := by
      simpa only [pow_add, mul_smul] using dist_triangle x ((g ^ m) • x) ((g ^ m) • ((g ^ n) • x))
    _ = dist x ((g ^ m) • x) + dist x ((g ^ n) • x) := by rw [(hi (g ^ m)).dist_eq]

lemma stableLength_tendsto (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) :
    Tendsto (fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ)) atTop (𝓝 (stableLengthAt x g)) := by
  have hb : BddBelow (Set.range (fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    positivity
  simpa only [Subadditive.lim, stableLengthAt] using (displacement_subadditive hi x g).tendsto_lim hb

lemma stableLength_nonneg (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : 0 ≤ stableLengthAt x g :=
  ge_of_tendsto' (stableLength_tendsto hi x g) (fun _ => by positivity)

lemma stableLength_le_displacement (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : stableLengthAt x g ≤ dist x (g • x) := by
  have hb : BddBelow (Set.range (fun n : ℕ => dist x ((g ^ n) • x) / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    positivity
  simpa only [Subadditive.lim, stableLengthAt, pow_one, Nat.cast_one, div_one] using
    (displacement_subadditive hi x g).lim_le_div hb (n := 1) (by decide)

lemma displacement_change_base (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g : G) : dist x (g • x) ≤ dist y (g • y) + 2 * dist x y := by
  have h₁ := dist_triangle x y (g • x)
  have h₂ := dist_triangle y (g • y) (g • x)
  rw [(hi g).dist_eq, dist_comm y x] at h₂
  linarith

lemma stableLength_basepoint (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g : G) : stableLengthAt x g = stableLengthAt y g := by
  suffices h : ∀ x y : X, stableLengthAt x g ≤ stableLengthAt y g from
    le_antisymm (h x y) (h y x)
  intro x y
  have he : Tendsto (fun n : ℕ => 2 * dist x y / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := le_of_tendsto_of_tendsto' (stableLength_tendsto hi x g)
    ((stableLength_tendsto hi y g).add he) (fun n => ?_)
  · simpa only [add_zero] using h
  · simpa only [add_div] using
      div_le_div_of_nonneg_right (displacement_change_base hi x y (g ^ n)) (Nat.cast_nonneg n)

lemma stableLength_one (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) :
    stableLengthAt x (1 : G) = 0 := by
  apply le_antisymm
  · simpa using stableLength_le_displacement hi x (1 : G)
  · exact stableLength_nonneg hi x 1

lemma stableLength_inv (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X) (g : G) :
    stableLengthAt x g⁻¹ = stableLengthAt x g := by
  apply tendsto_nhds_unique (stableLength_tendsto hi x g⁻¹)
  convert stableLength_tendsto hi x g using 1
  ext n
  congr 1
  rw [← (hi (g ^ n)).dist_eq x ((g⁻¹ ^ n) • x)]
  simp only [← mul_smul, inv_pow, mul_inv_cancel, one_smul, dist_comm]

lemma stableLength_conjugate (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g h : G) : stableLengthAt x (h * g * h⁻¹) = stableLengthAt x g := by
  have hc : ∀ n : ℕ, dist x (((h * g * h⁻¹) ^ n) • x) =
      dist (h⁻¹ • x) ((g ^ n) • (h⁻¹ • x)) := by
    intro n
    rw [← (hi h⁻¹).dist_eq x (((h * g * h⁻¹) ^ n) • x)]
    rw [conj_pow]
    simp only [mul_smul, inv_smul_smul]
  have ht := stableLength_tendsto hi (h⁻¹ • x) g
  simp only [← hc] at ht
  rw [stableLength_basepoint hi (h⁻¹ • x) x g] at ht
  exact tendsto_nhds_unique (stableLength_tendsto hi x (h * g * h⁻¹)) ht

lemma stableLength_pow (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (k : ℕ) : stableLengthAt x (g ^ k) = k * stableLengthAt x g := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [stableLength_one hi]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsub : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
  have ht := (stableLength_tendsto hi x g).comp hsub
  have ht' := ht.const_mul (k : ℝ)
  apply tendsto_nhds_unique (stableLength_tendsto hi x (g ^ k))
  convert ht' using 1
  ext n
  simp only [Function.comp_apply, ← pow_mul, Nat.cast_mul]
  field_simp

lemma stableLength_mul_le (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) {g h : G} (hc : Commute g h) :
    stableLengthAt x (g * h) ≤ stableLengthAt x g + stableLengthAt x h := by
  apply le_of_tendsto_of_tendsto' (stableLength_tendsto hi x (g * h))
    ((stableLength_tendsto hi x g).add (stableLength_tendsto hi x h))
  intro n
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [hc.mul_pow, mul_smul]
  have htri := dist_triangle x ((g ^ n) • x) ((g ^ n) • ((h ^ n) • x))
  simpa only [(hi (g ^ n)).dist_eq] using htri

lemma displacement_inv (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : dist x (g⁻¹ • x) = dist x (g • x) := by
  rw [← (hi g).dist_eq x (g⁻¹ • x), smul_inv_smul, dist_comm]

lemma action_dist (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g h : G) : dist (g • x) (h • x) = dist x ((g⁻¹ * h) • x) := by
  rw [← (hi g⁻¹).dist_eq (g • x) (h • x), inv_smul_smul, mul_smul]

lemma commuting_displacement_quadrilateral (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    dist x ((g * h) • x) ^ 2 + dist x ((g * h⁻¹) • x) ^ 2 ≤
      2 * dist x (g • x) ^ 2 + 2 * dist x (h • x) ^ 2 := by
  have hq := quadrilateral hX x (g • x) ((g * h) • x) (h • x)
  have h₁ : dist (g • x) ((g * h) • x) = dist x (h • x) := by
    rw [mul_smul, (hi g).dist_eq]
  have h₂ : dist ((g * h) • x) (h • x) = dist x (g • x) := by
    rw [hc.eq, mul_smul, (hi h).dist_eq, dist_comm]
  have h₃ : dist (g • x) (h • x) = dist x ((g * h⁻¹) • x) := by
    rw [action_dist hi, ← displacement_inv hi x (g⁻¹ * h)]
    simp only [mul_inv_rev, inv_inv, ← hc.inv_right.eq]
  rw [h₁, h₂, h₃, dist_comm (h • x) x] at hq
  linarith

lemma length_parallelogram_le (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    stableLengthAt x (g * h) ^ 2 + stableLengthAt x (g * h⁻¹) ^ 2 ≤
      2 * stableLengthAt x g ^ 2 + 2 * stableLengthAt x h ^ 2 := by
  apply le_of_tendsto_of_tendsto'
    (((stableLength_tendsto hi x (g * h)).pow 2).add ((stableLength_tendsto hi x (g * h⁻¹)).pow 2))
    ((((stableLength_tendsto hi x g).pow 2).const_mul 2).add
      (((stableLength_tendsto hi x h).pow 2).const_mul 2))
  intro n
  have hd := commuting_displacement_quadrilateral hX hi x (hc.pow_pow n n)
  have hdiv := div_le_div_of_nonneg_right hd (sq_nonneg (n : ℝ))
  simpa only [div_pow, hc.mul_pow, hc.inv_right.mul_pow, inv_pow, add_div, mul_div_assoc] using hdiv

lemma length_parallelogram (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    stableLengthAt x (g * h) ^ 2 + stableLengthAt x (g * h⁻¹) ^ 2 =
      2 * stableLengthAt x g ^ 2 + 2 * stableLengthAt x h ^ 2 := by
  have h₁ := length_parallelogram_le hX hi x hc
  have hcomm : Commute (g * h) (g * h⁻¹) :=
    (Commute.refl g).mul_left hc.symm |>.mul_right (hc.inv_right.mul_left (Commute.refl h).inv_right)
  have he₁ : (g * h) * (g * h⁻¹) = g ^ 2 := by
    calc (g * h) * (g * h⁻¹) = g * (h * g) * h⁻¹ := by group
         _ = g * (g * h) * h⁻¹ := by rw [hc.symm.eq]
         _ = g ^ 2 := by simp only [pow_two]; group
  have he₂ : (g * h) * (g * h⁻¹)⁻¹ = h ^ 2 := by
    calc (g * h) * (g * h⁻¹)⁻¹ = g * (h * h) * g⁻¹ := by group
         _ = (h * h) * g * g⁻¹ := by rw [(hc.mul_right hc).eq]
         _ = h ^ 2 := by simp only [pow_two]; group
  have h₂ := length_parallelogram_le hX hi x hcomm
  rw [he₁, he₂, stableLength_pow hi, stableLength_pow hi] at h₂
  norm_num at h₂
  nlinarith

noncomputable def lengthPairing (x : X) (g h : G) : ℝ :=
  (stableLengthAt x (g * h) ^ 2 - stableLengthAt x g ^ 2 - stableLengthAt x h ^ 2) / 2

lemma lengthPairing_symmetric (x : X) {g h : G} (hc : Commute g h) :
    lengthPairing x g h = lengthPairing x h g := by
  unfold lengthPairing
  rw [hc.eq]
  ring

lemma lengthPairing_self (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : lengthPairing x g g = stableLengthAt x g ^ 2 := by
  unfold lengthPairing
  rw [← pow_two, stableLength_pow hi]
  norm_num
  ring

lemma lengthPairing_one (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) : lengthPairing x g 1 = 0 := by
  simp [lengthPairing, stableLength_one hi]

lemma lengthPairing_polarization (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    lengthPairing x g h =
      (stableLengthAt x (g * h) ^ 2 - stableLengthAt x (g * h⁻¹) ^ 2) / 4 := by
  unfold lengthPairing
  linarith [length_parallelogram hX hi x hc]

lemma lengthPairing_inv (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) :
    lengthPairing x g h⁻¹ = -lengthPairing x g h := by
  rw [lengthPairing_polarization hX hi x hc.inv_right,
    lengthPairing_polarization hX hi x hc, inv_inv]
  ring

lemma lengthPairing_conjugate (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g h k : G) :
    lengthPairing x (k * g * k⁻¹) (k * h * k⁻¹) = lengthPairing x g h := by
  have he : (k * g * k⁻¹) * (k * h * k⁻¹) = k * (g * h) * k⁻¹ := by group
  simp only [lengthPairing, he, stableLength_conjugate hi]

lemma lengthPairing_jensen (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h k : G} (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) :
    lengthPairing x (g * h) k + lengthPairing x (g * h⁻¹) k =
      2 * lengthPairing x g k := by
  rw [lengthPairing_polarization hX hi x (hgk.mul_left hhk),
    lengthPairing_polarization hX hi x (hgk.mul_left hhk.inv_left),
    lengthPairing_polarization hX hi x hgk]
  have h₁ := length_parallelogram hX hi x (hgh.mul_left hhk.symm)
  have h₂ := length_parallelogram hX hi x (hgh.mul_left hhk.symm.inv_left)
  have e₁ : g * k * h = g * h * k := by rw [mul_assoc, hhk.symm.eq, ← mul_assoc]
  have e₂ : g * k * h⁻¹ = g * h⁻¹ * k := by rw [mul_assoc, hhk.symm.inv_right.eq, ← mul_assoc]
  have e₃ : g * k⁻¹ * h = g * h * k⁻¹ := by rw [mul_assoc, hhk.symm.inv_left.eq, ← mul_assoc]
  have e₄ : g * k⁻¹ * h⁻¹ = g * h⁻¹ * k⁻¹ := by rw [mul_assoc, hhk.symm.inv_left.inv_right.eq, ← mul_assoc]
  rw [e₁, e₂] at h₁
  rw [e₃, e₄] at h₂
  linarith

lemma lengthPairing_mul_left (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h k : G} (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) :
    lengthPairing x (g * h) k = lengthPairing x g k + lengthPairing x h k := by
  have h₁ := lengthPairing_jensen hX hi x hgh hgk hhk
  have h₂ := lengthPairing_jensen hX hi x hgh.symm hhk hgk
  have he : h * g⁻¹ = (g * h⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv]
  have he' : lengthPairing x (h * g⁻¹) k = -lengthPairing x (g * h⁻¹) k := by
    rw [he, lengthPairing_symmetric x (hgk.mul_left hhk.inv_left).inv_left,
      lengthPairing_inv hX hi x (hgk.mul_left hhk.inv_left).symm,
      lengthPairing_symmetric x (hgk.mul_left hhk.inv_left).symm]
  rw [← hgh.eq, he'] at h₂
  linarith

lemma lengthPairing_mul_right (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h k : G} (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) :
    lengthPairing x g (h * k) = lengthPairing x g h + lengthPairing x g k := by
  rw [lengthPairing_symmetric x (hgh.mul_right hgk),
    lengthPairing_mul_left hX hi x hhk hgh.symm hgk.symm,
    lengthPairing_symmetric x hgh.symm, lengthPairing_symmetric x hgk.symm]

lemma lengthPairing_pow_right (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℕ) :
    lengthPairing x g (h ^ n) = n * lengthPairing x g h := by
  induction n with
  | zero => simp [lengthPairing_one hi]
  | succ n hn =>
    rw [pow_succ, lengthPairing_mul_right hX hi x (hc.pow_right n) hc (Commute.self_pow h n).symm, hn]
    push_cast
    ring

lemma lengthPairing_pow_left (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℕ) :
    lengthPairing x (g ^ n) h = n * lengthPairing x g h := by
  rw [lengthPairing_symmetric x (hc.pow_left n), lengthPairing_pow_right hX hi x hc.symm,
    lengthPairing_symmetric x hc.symm]

lemma stableLength_product_sq (x : X) (g h : G) :
    stableLengthAt x (g * h) ^ 2 =
      stableLengthAt x g ^ 2 + stableLengthAt x h ^ 2 + 2 * lengthPairing x g h := by
  unfold lengthPairing
  ring

lemma stableLength_zpow (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (n : ℤ) : stableLengthAt x (g ^ n) = |(n : ℝ)| * stableLengthAt x g := by
  cases n with
  | ofNat n => simp [stableLength_pow hi]
  | negSucc n =>
    rw [show (Int.negSucc n : ℝ) = -((n : ℝ) + 1) by simp [Int.cast_negSucc],
      abs_neg, abs_of_nonneg (by positivity)]
    simp [zpow_negSucc, stableLength_inv hi, stableLength_pow hi]

lemma lengthPairing_zpow_right (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℤ) :
    lengthPairing x g (h ^ n) = n * lengthPairing x g h := by
  cases n with
  | ofNat n => simp [lengthPairing_pow_right hX hi x hc]
  | negSucc n =>
    simp [zpow_negSucc, lengthPairing_inv hX hi x (hc.pow_right _),
      lengthPairing_pow_right hX hi x hc, Int.cast_negSucc]
    ring

end StableLengths

section CompactAttainment

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X] [ProperSpace X]

lemma finite_movers_of_compact
    (hp : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite)
    {K : Set X} (hK : IsCompact K) (o : X) (A : ℝ) (hA : 0 ≤ A) :
    {g : G | ∃ p ∈ K, dist p (g • p) ≤ A}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall o
  refine (hp (Metric.closedBall o (R + A)) (isCompact_closedBall o (R + A))).subset ?_
  rintro g ⟨p, hpK, hdist⟩
  have hpR := hR hpK
  change dist p o ≤ R at hpR
  have hgR : dist (g • p) o ≤ R + A := by
    have ht := dist_triangle (g • p) p o
    rw [dist_comm (g • p) p] at ht
    linarith
  refine ⟨g • p, ⟨p, ?_, rfl⟩, hgR⟩
  change dist p o ≤ R + A
  linarith

lemma exists_displacement_minimizer [Nonempty X] (hG : GeometricAction G X) (g : G) :
    ∃ x : X, ∀ y : X, dist x (g • x) ≤ dist y (g • y) := by
  classical
  let hi := hG.2.1
  let o : X := Classical.choice inferInstance
  let A := dist o (g • o)
  have hA : 0 ≤ A := dist_nonneg
  obtain ⟨K, hK, hcover⟩ := hG.2.2.2
  let Q : Set G := {q | (∃ p ∈ K, dist p (q • p) ≤ A) ∧ ∃ h : G, h⁻¹ * g * h = q}
  have hQ : Q.Finite := (finite_movers_of_compact hG.2.2.1 hK o A hA).subset
    (fun _ hq => hq.1)
  let S : Set ℝ := ⋃ q ∈ Q, (fun p : X => dist p (q • p)) '' K
  have hS : IsCompact S := hQ.isCompact_biUnion (fun q _ => hK.image (continuous_id.dist (hi q).continuous))
  have hnear : ∀ y : X, dist y (g • y) ≤ A → dist y (g • y) ∈ S := by
    intro y hdy
    obtain ⟨h, p, hp, rfl⟩ := hcover y
    have hd : dist p ((h⁻¹ * g * h) • p) = dist (h • p) (g • (h • p)) := by
      rw [← (hi h).dist_eq]
      simp only [mul_smul, smul_inv_smul]
    apply Set.mem_iUnion.mpr
    refine ⟨h⁻¹ * g * h, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact ⟨⟨p, hp, hd ▸ hdy⟩, h, rfl⟩
    · exact ⟨p, hp, hd⟩
  have ho : A ∈ S := hnear o le_rfl
  obtain ⟨a, ha, hmin⟩ := hS.exists_isMinOn ⟨A, ho⟩ continuous_id.continuousOn
  obtain ⟨q, hq, p, hp, rfl⟩ := Set.mem_iUnion₂.mp ha
  obtain ⟨h, hh⟩ := hq.2
  have hd : dist (h • p) (g • (h • p)) = dist p (q • p) := by
    rw [← hh, ← (hi h).dist_eq p ((h⁻¹ * g * h) • p)]
    simp only [mul_smul, smul_inv_smul]
  refine ⟨h • p, fun y => ?_⟩
  rw [hd]
  by_cases hy : dist y (g • y) ≤ A
  · exact hmin (hnear y hy)
  · exact (hmin ho).trans (le_of_lt (lt_of_not_ge hy))

end CompactAttainment

section AxialLengths

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

lemma segment_point_eq_of_dist (hX : CAT0 X) {a b c : X} {γ : ℝ → X}
    (hγ : Segment a c γ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hab : dist a b = t * dist a c) (hbc : dist b c = (1 - t) * dist a c) :
    γ t = b := by
  obtain ⟨η, hη⟩ := hX.1 a b
  have hc := hX.2 a c b γ η hγ hη t ht 1 (by constructor <;> norm_num)
  rw [hη.2.1, dist_comm c b, hab, hbc] at hc
  have he : (t ^ 2 - t * 1) * dist a c ^ 2 +
      ((1 : ℝ)^2 - t * 1) * (t * dist a c)^2 +
      t * 1 * ((1 - t) * dist a c)^2 = 0 := by ring
  rw [he] at hc
  have hd : dist (γ t) b = 0 := by nlinarith [dist_nonneg (x := γ t) (y := b)]
  exact dist_eq_zero.mp hd

lemma minimizer_displacement_two (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (g : G) {x : X}
    (hm : ∀ y : X, dist x (g • x) ≤ dist y (g • y)) :
    dist x ((g ^ 2) • x) = 2 * dist x (g • x) := by
  obtain ⟨γ, hγ⟩ := hX.1 x (g • x)
  have hη := segment_isometry hγ (hi g)
  have hd := comparison_common_start hX (segment_reverse hγ) hη
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Function.comp_apply] at hd
  have hlow := hm (γ (1 / 2))
  have hu := dist_triangle x (g • x) (g • (g • x))
  rw [(hi g).dist_eq] at hu
  rw [pow_two, mul_smul]
  linarith

lemma powerStepDistance (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (n : ℕ) :
    dist ((g ^ n) • x) ((g ^ (n + 1)) • x) = dist x (g • x) := by
  rw [pow_succ, mul_smul, (hi (g ^ n)).dist_eq]

lemma extension_numeric {D R N : ℝ} (hN : 0 < N)
    (hc : (2 * D) ^ 2 ≤ ((1 / N) ^ 2 - (1 / N) * 1) * (N * D) ^ 2 +
      ((1 : ℝ)^2 - (1 / N) * 1) * D^2 + (1 / N) * 1 * R^2) :
    ((N + 1) * D) ^ 2 ≤ R ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hc hN.le
  have he : N * (((1 / N) ^ 2 - (1 / N) * 1) * (N * D) ^ 2 +
      ((1 : ℝ)^2 - (1 / N) * 1) * D^2 + (1 / N) * 1 * R^2) =
      (2 * N - N ^ 2 - 1) * D^2 + R^2 := by
    field_simp
    ring
  rw [he] at h
  nlinarith

lemma minimizer_displacement_pow (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (g : G) {x : X}
    (hm : ∀ y : X, dist x (g • x) ≤ dist y (g • y)) (n : ℕ) :
    dist x ((g ^ n) • x) = n * dist x (g • x) := by
  have htwo := minimizer_displacement_two hX hi g hm
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
    let D := dist x (g • x)
    let N : ℝ := n + 1
    have hN : 0 < N := by dsimp [N]; positivity
    have htrad : (1 / N : ℝ) ∈ Set.Icc 0 1 := by
      constructor
      · positivity
      · apply (div_le_one hN).mpr
        dsimp [N]
        linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨γ, hγ⟩ := hX.1 ((g ^ (n + 1)) • x) x
    have hγd : dist ((g ^ (n + 1)) • x) x = N * D := by rw [dist_comm, hn1]; simp [N, D]
    have hγt : γ (1 / N) = (g ^ n) • x := by
      apply segment_point_eq_of_dist hX hγ htrad
      · rw [dist_comm, powerStepDistance hi, hγd]
        change D = 1 / N * (N * D)
        field_simp
      · rw [dist_comm, hn, hγd]
        change (n : ℝ) * D = (1 - 1 / N) * (N * D)
        rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul, mul_div_cancel_left₀ _ hN.ne']
        dsimp [N]
        ring
    obtain ⟨η, hη⟩ := hX.1 ((g ^ (n + 1)) • x) ((g ^ (n + 2)) • x)
    have hc := hX.2 ((g ^ (n + 1)) • x) x ((g ^ (n + 2)) • x)
      γ η hγ hη (1 / N) htrad 1 (by constructor <;> norm_num)
    have hnext : dist ((g ^ (n + 1)) • x) ((g ^ (n + 2)) • x) = D :=
      powerStepDistance hi x g (n + 1)
    have hlocal : dist ((g ^ n) • x) ((g ^ (n + 2)) • x) = 2 * D := by
      rw [pow_add, mul_smul, (hi (g ^ n)).dist_eq, htwo]
    rw [hγt, hη.2.1, hlocal, hγd, hnext] at hc
    have hlo := extension_numeric hN hc
    have hup := dist_triangle x ((g ^ (n + 1)) • x) ((g ^ (n + 2)) • x)
    rw [hn1, hnext] at hup
    have he : ((n + 2 : ℕ) : ℝ) * D = (N + 1) * D := by push_cast; dsimp [N]; ring
    change dist x ((g ^ (n + 2)) • x) = ((n + 2 : ℕ) : ℝ) * D
    rw [he]
    have hp : 0 ≤ (N + 1) * D := mul_nonneg (by linarith) dist_nonneg
    have hu : dist x ((g ^ (n + 2)) • x) ≤ (N + 1) * D := by
      dsimp [N]
      push_cast at hup
      linarith
    nlinarith [dist_nonneg (x := x) (y := (g ^ (n + 2)) • x)]

open Filter Topology

lemma stableLength_minimizer (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (g : G) {x : X}
    (hm : ∀ y : X, dist x (g • x) ≤ dist y (g • y)) :
    stableLengthAt x g = dist x (g • x) := by
  apply tendsto_nhds_unique (stableLength_tendsto hi x g)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [minimizer_displacement_pow hX hi g hm]
  simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

lemma lengthPairing_basepoint (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g h : G) : lengthPairing x g h = lengthPairing y g h := by
  simp only [lengthPairing, stableLength_basepoint hi x y]

lemma stableLength_finiteOrder (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) {g : G} (hg : IsOfFinOrder g) : stableLengthAt x g = 0 := by
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  have hp := stableLength_pow hi x g n
  rw [he, stableLength_one hi] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (ne_of_gt (Nat.cast_pos.mpr hn))

lemma finiteOrder_of_fixedPoint
    (hp : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite)
    (x : X) {g : G} (hg : g • x = x) : IsOfFinOrder g := by
  have hstab : (MulAction.stabilizer G x : Set G).Finite := by
    refine (hp {x} isCompact_singleton).subset ?_
    intro h hh
    exact ⟨x, ⟨x, Set.mem_singleton x, hh⟩, Set.mem_singleton x⟩
  let : Finite (MulAction.stabilizer G x) := hstab.to_subtype
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp
    (isOfFinOrder_of_finite (⟨g, hg⟩ : MulAction.stabilizer G x))
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  exact congrArg Subtype.val he

lemma stableLength_eq_zero_iff_finiteOrder [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (x : X) (g : G) :
    stableLengthAt x g = 0 ↔ IsOfFinOrder g := by
  refine ⟨fun hzero => ?_, stableLength_finiteOrder hG.2.1 x⟩
  obtain ⟨p, hp⟩ := exists_displacement_minimizer hG g
  rw [stableLength_basepoint hG.2.1 x p g, stableLength_minimizer hG.1 hG.2.1 g hp] at hzero
  exact finiteOrder_of_fixedPoint hG.2.2.1 p (dist_eq_zero.mp hzero).symm

lemma lengthPairing_zpow_left (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℤ) :
    lengthPairing x (g ^ n) h = n * lengthPairing x g h := by
  rw [lengthPairing_symmetric x (hc.zpow_left n), lengthPairing_zpow_right hX hi x hc.symm,
    lengthPairing_symmetric x hc.symm]

lemma stableLength_zpow_product_sq (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (n : ℤ) :
    stableLengthAt x ((g ^ n) * h) ^ 2 =
      (n : ℝ)^2 * stableLengthAt x g ^ 2 + stableLengthAt x h ^ 2 +
        2 * (n : ℝ) * lengthPairing x g h := by
  rw [stableLength_product_sq, stableLength_zpow hi, lengthPairing_zpow_left hX hi x hc,
    mul_pow, sq_abs]
  ring

lemma nonpos_of_nat_mul_le {a b : ℝ} (h : ∀ n : ℕ, (n : ℝ) * a ≤ b) : a ≤ 0 := by
  by_contra! ha
  obtain ⟨n, hn⟩ := exists_nat_gt (b / a)
  exact (not_lt_of_ge (h n)) ((div_lt_iff₀ ha).mp hn)

lemma zero_of_int_mul_le {a b : ℝ} (h : ∀ n : ℤ, (n : ℝ) * a ≤ b) : a = 0 := by
  have h₁ := nonpos_of_nat_mul_le (fun n => h n)
  have h₂ : -a ≤ 0 := nonpos_of_nat_mul_le (b := b) (fun n => by
    have hn := h (-(n : ℤ))
    push_cast at hn
    nlinarith)
  linarith

lemma lengthPairing_zero_of_length_zero (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (x : X)
    {g h : G} (hc : Commute g h) (hzero : stableLengthAt x g = 0) :
    lengthPairing x g h = 0 := by
  have hz : -2 * lengthPairing x g h = 0 := zero_of_int_mul_le
    (b := stableLengthAt x h ^ 2) (fun n => by
      have he := stableLength_zpow_product_sq hX hi x hc n
      rw [hzero] at he
      nlinarith [sq_nonneg (stableLengthAt x ((g ^ n) * h))])
  linarith

end AxialLengths

end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

section BusemannCharacter

open Filter Topology

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

/-- Busemann function based on the positive orbit of a minimizing point. -/
noncomputable def orbitBusemann (x : X) (g : G) (D : ℝ) (z : X) : ℝ :=
  ⨅ n : ℕ, dist z ((g ^ n) • x) - (n : ℝ) * D

lemma orbitBusemann_tendsto (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    (z : X) :
    Tendsto (fun n : ℕ => dist z ((g ^ n) • x) - (n : ℝ) * D)
      atTop (𝓝 (orbitBusemann x g D z)) := by
  have hD : dist x (g • x) = D := by simpa using haxis 1
  apply tendsto_atTop_ciInf
  · apply antitone_nat_of_succ_le
    intro n
    have ht := dist_triangle z ((g ^ n) • x) ((g ^ (n + 1)) • x)
    rw [powerStepDistance hi, hD] at ht
    push_cast
    linarith
  · refine ⟨-dist z x, ?_⟩
    rintro _ ⟨n, rfl⟩
    have ht := dist_triangle x z ((g ^ n) • x)
    rw [haxis n, dist_comm x z] at ht
    linarith

lemma orbitBusemann_lipschitz (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    (z w : X) : |orbitBusemann x g D z - orbitBusemann x g D w| ≤ dist z w := by
  apply le_of_tendsto' (((orbitBusemann_tendsto hi x g D haxis z).sub
    (orbitBusemann_tendsto hi x g D haxis w)).abs)
  intro n
  simpa only [sub_sub_sub_cancel_right] using abs_dist_sub_le z w ((g ^ n) • x)

lemma fourSquares_limit {A B C E : ℕ → ℝ} {a b c e D : ℝ}
    (hA : Tendsto (fun n : ℕ => A n - n * D) atTop (𝓝 a))
    (hB : Tendsto (fun n : ℕ => B n - n * D) atTop (𝓝 b))
    (hC : Tendsto (fun n : ℕ => C n - n * D) atTop (𝓝 c))
    (hE : Tendsto (fun n : ℕ => E n - n * D) atTop (𝓝 e)) :
    Tendsto (fun n : ℕ => (A n ^ 2 + B n ^ 2 - C n ^ 2 - E n ^ 2) / (n : ℝ))
      atTop (𝓝 (2 * D * (a + b - c - e))) := by
  have hs := ((((hA.pow 2).add (hB.pow 2)).sub (hC.pow 2)).sub (hE.pow 2)).div_atTop
    tendsto_natCast_atTop_atTop
  have hl := ((((hA.add hB).sub hC).sub hE).const_mul (2 * D)).add hs
  simp only [add_zero] at hl
  refine Tendsto.congr' ?_ hl
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp
  ring

lemma quadrilateral_difference (hX : CAT0 X) (z w p q : X) :
    |dist z p ^ 2 + dist w q ^ 2 - dist w p ^ 2 - dist z q ^ 2| ≤
      dist z w ^ 2 + dist p q ^ 2 := by
  have h₁ := quadrilateral hX z w p q
  have h₂ := quadrilateral hX w z p q
  rw [dist_comm q z] at h₁
  rw [dist_comm q w, dist_comm w z] at h₂
  rw [abs_le]
  constructor <;> linarith

lemma orbitBusemann_centralizer_difference (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) (z w : X) :
    orbitBusemann x g D (h • z) - orbitBusemann x g D (h • w) =
      orbitBusemann x g D z - orbitBusemann x g D w := by
  let p : ℕ → X := fun n => (g ^ n) • x
  let q : ℕ → X := fun n => h⁻¹ • p n
  have hq (v : X) (n : ℕ) : dist v (q n) = dist (h • v) (p n) := by
    rw [← (hi h).dist_eq]
    dsimp [q]
    rw [smul_inv_smul]
  have hpq (n : ℕ) : dist (p n) (q n) = dist x (h⁻¹ • x) := by
    dsimp [p, q]
    rw [← mul_smul, ← (hc.pow_left n).inv_right.eq, mul_smul, (hi (g ^ n)).dist_eq]
  have hl := fourSquares_limit (orbitBusemann_tendsto hi x g D haxis z)
    (orbitBusemann_tendsto hi x g D haxis (h • w))
    (orbitBusemann_tendsto hi x g D haxis w)
    (orbitBusemann_tendsto hi x g D haxis (h • z))
  have hu : ∀ n : ℕ,
      |(dist z (p n)^2 + dist (h • w) (p n)^2 - dist w (p n)^2 - dist (h • z) (p n)^2) / (n : ℝ)|
        ≤ (dist z w ^ 2 + dist x (h⁻¹ • x)^2) / (n : ℝ) := by
    intro n
    have hquad := quadrilateral_difference hX z w (p n) (q n)
    rw [hq, hq, hpq] at hquad
    rw [abs_div, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    exact div_le_div_of_nonneg_right hquad (Nat.cast_nonneg n)
  have hz := le_of_tendsto_of_tendsto' hl.abs
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop) hu
  have hzero : 2 * D * (orbitBusemann x g D z + orbitBusemann x g D (h • w) -
      orbitBusemann x g D w - orbitBusemann x g D (h • z)) = 0 := by
    exact abs_nonpos_iff.mp hz
  have he := (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) hD.ne')
  linarith

noncomputable def orbitCharacter (x : X) (g : G) (D : ℝ) (h : G) : ℝ :=
  orbitBusemann x g D x - orbitBusemann x g D (h • x)

lemma orbitCharacter_one (x : X) (g : G) (D : ℝ) : orbitCharacter x g D 1 = 0 := by
  simp [orbitCharacter]

lemma orbitCharacter_mul (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h k : G} (hc : Commute g h) :
    orbitCharacter x g D (h * k) = orbitCharacter x g D h + orbitCharacter x g D k := by
  have he := orbitBusemann_centralizer_difference hX hi x g D hD haxis hc (k • x) x
  dsimp [orbitCharacter]
  rw [mul_smul]
  linarith

lemma orbitCharacter_pow (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) (n : ℕ) :
    orbitCharacter x g D (h ^ n) = n * orbitCharacter x g D h := by
  induction n with
  | zero => simp [orbitCharacter_one]
  | succ n ih =>
    rw [pow_succ, orbitCharacter_mul hX hi x g D hD haxis (hc.pow_right n), ih]
    push_cast
    ring

lemma orbitCharacter_inv (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) :
    orbitCharacter x g D h⁻¹ = -orbitCharacter x g D h := by
  have he := orbitCharacter_mul hX hi x g D hD haxis (k := h⁻¹) hc
  rw [mul_inv_cancel, orbitCharacter_one] at he
  linarith

lemma orbitCharacter_zpow (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) (n : ℤ) :
    orbitCharacter x g D (h ^ n) = n * orbitCharacter x g D h := by
  cases n with
  | ofNat n => simpa using orbitCharacter_pow hX hi x g D hD haxis hc n
  | negSucc n =>
    rw [zpow_negSucc, orbitCharacter_inv hX hi x g D hD haxis (hc.pow_right (n+1)),
      orbitCharacter_pow hX hi x g D hD haxis hc]
    push_cast
    ring

lemma orbitBusemann_self (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D) :
    orbitBusemann x g D x = 0 := by
  have he := orbitBusemann_tendsto hi x g D haxis x
  simp only [haxis, sub_self] at he
  exact tendsto_nhds_unique he tendsto_const_nhds

lemma orbitCharacter_self (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D) :
    orbitCharacter x g D g = D := by
  have he := (orbitBusemann_tendsto hi x g D haxis (g • x)).comp (tendsto_add_atTop_nat 1)
  have hd (n : ℕ) : dist (g • x) ((g ^ (n+1)) • x) = n * D := by
    rw [pow_succ', mul_smul, (hi g).dist_eq, haxis]
  have he' : orbitBusemann x g D (g • x) = -D := by
    apply tendsto_nhds_unique he
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => -D) atTop (𝓝 (-D))) using 1
    ext n
    dsimp only [Function.comp_apply]
    rw [hd, Nat.cast_add_one]
    ring
  simp [orbitCharacter, orbitBusemann_self hi x g D haxis, he']

lemma orbitCharacter_abs_le (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    {h : G} (hc : Commute g h) : |orbitCharacter x g D h| ≤ stableLengthAt x h := by
  apply ge_of_tendsto (stableLength_tendsto hi x h)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have he := orbitBusemann_lipschitz hi x g D haxis x ((h ^ n) • x)
  change |orbitCharacter x g D (h ^ n)| ≤ _ at he
  rw [orbitCharacter_pow hX hi x g D hD haxis hc, abs_mul,
    show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)] at he
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using he)

lemma lengthPairing_eq_orbitCharacter (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x : X) (g : G) (D : ℝ) (hD : 0 < D)
    (haxis : ∀ n : ℕ, dist x ((g ^ n) • x) = n * D)
    (hL : stableLengthAt x g = D) {h : G} (hc : Commute g h) :
    lengthPairing x g h = D * orbitCharacter x g D h := by
  have he : 2 * (D * orbitCharacter x g D h - lengthPairing x g h) = 0 :=
    zero_of_int_mul_le (b := stableLengthAt x h ^ 2 - orbitCharacter x g D h ^ 2) (fun n => by
      have hb := orbitCharacter_abs_le hX hi x g D hD haxis
        ((Commute.refl g).zpow_right n |>.mul_right hc)
      rw [orbitCharacter_mul hX hi x g D hD haxis ((Commute.refl g).zpow_right n),
        orbitCharacter_zpow hX hi x g D hD haxis (Commute.refl g),
        orbitCharacter_self hi x g D haxis] at hb
      have hs : ((n : ℝ) * D + orbitCharacter x g D h)^2 ≤
          stableLengthAt x ((g ^ n) * h)^2 := by
        nlinarith [sq_abs ((n : ℝ) * D + orbitCharacter x g D h),
          stableLength_nonneg hi x ((g ^ n) * h), abs_nonneg ((n : ℝ) * D + orbitCharacter x g D h)]
      rw [stableLength_zpow_product_sq hX hi x hc, hL] at hs
      nlinarith)
  linarith

lemma lengthPairing_centralizer [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (x : X) {g h k : G}
    (hgh : Commute g h) (hgk : Commute g k) :
    lengthPairing x g (h * k) = lengthPairing x g h + lengthPairing x g k := by
  by_cases hz : stableLengthAt x g = 0
  · rw [lengthPairing_zero_of_length_zero hG.1 hG.2.1 x (hgh.mul_right hgk) hz,
      lengthPairing_zero_of_length_zero hG.1 hG.2.1 x hgh hz,
      lengthPairing_zero_of_length_zero hG.1 hG.2.1 x hgk hz]
    ring
  obtain ⟨p, hp⟩ := exists_displacement_minimizer hG g
  have hLp := stableLength_minimizer hG.1 hG.2.1 g hp
  have hD : 0 < dist p (g • p) := by
    have ht := stableLength_nonneg hG.2.1 x g
    rw [stableLength_basepoint hG.2.1 x p g, hLp] at hz ht
    exact lt_of_le_of_ne ht (Ne.symm hz)
  have haxis := minimizer_displacement_pow hG.1 hG.2.1 g hp
  rw [lengthPairing_basepoint hG.2.1 x p,
    lengthPairing_basepoint hG.2.1 x p g h, lengthPairing_basepoint hG.2.1 x p g k]
  rw [lengthPairing_eq_orbitCharacter hG.1 hG.2.1 p g _ hD haxis hLp (hgh.mul_right hgk),
    lengthPairing_eq_orbitCharacter hG.1 hG.2.1 p g _ hD haxis hLp hgh,
    lengthPairing_eq_orbitCharacter hG.1 hG.2.1 p g _ hD haxis hLp hgk,
    orbitCharacter_mul hG.1 hG.2.1 p g _ hD haxis hgh, mul_add]

end BusemannCharacter

end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

section BraidAlgebra

variable {G : Type*} [Group G]

/-- The length-three and distant commutation relations on m successive letters.
The letters are zero-indexed here. -/
def BraidRelations (m : ℕ) (s : ℕ → G) : Prop :=
  (∀ i, i + 1 < m → s i * s (i+1) * s i = s (i+1) * s i * s (i+1)) ∧
  (∀ i j, i < m → j < m → i + 2 ≤ j → Commute (s i) (s j))

def braidLoop (s : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => s n * braidLoop s n * s n

def braidCenter (s : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => braidCenter s n * braidLoop s (n+1)

def braidDelta (s : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => braidDelta s n * s n

lemma commute_braidLoop {g : G} {s : ℕ → G} {n : ℕ}
    (hc : ∀ i < n, Commute g (s i)) : Commute g (braidLoop s n) := by
  induction n with
  | zero => exact Commute.one_right g
  | succ n ih =>
    exact ((hc n (by omega)).mul_right (ih (fun i hi => hc i (by omega)))).mul_right
      (hc n (by omega))

lemma commute_braidCenter {g : G} {s : ℕ → G} {n : ℕ}
    (hc : ∀ i < n, Commute g (s i)) : Commute g (braidCenter s n) := by
  induction n with
  | zero => exact Commute.one_right g
  | succ n ih =>
    exact (ih (fun i hi => hc i (by omega))).mul_right (commute_braidLoop hc)

lemma commute_braidDelta {g : G} {s : ℕ → G} {n : ℕ}
    (hc : ∀ i < n, Commute g (s i)) : Commute g (braidDelta s n) := by
  induction n with
  | zero => exact Commute.one_right g
  | succ n ih =>
    exact (ih (fun i hi => hc i (by omega))).mul_right (hc n (by omega))

lemma braid_loop_step {a b C : G} (hab : a*b*a = b*a*b) (hbC : Commute b C) :
    Commute a (b * (a*C*a) * b) := by
  change a * (b * (a*C*a) * b) = b * (a*C*a) * b * a
  calc
    a * (b * (a*C*a) * b) = (a*b*a)*C*a*b := by group
    _ = (b*a*b)*C*a*b := by rw [hab]
    _ = b*a*(b*C)*a*b := by group
    _ = b*a*(C*b)*a*b := by rw [hbC.eq]
    _ = b*a*C*(b*a*b) := by group
    _ = b*a*C*(a*b*a) := by rw [← hab]
    _ = b * (a*C*a) * b * a := by group

lemma braidLoop_commute {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n i : ℕ} (hn : n ≤ m) (hi : i + 1 < n) : Commute (s i) (braidLoop s n) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more k ih₀ ih₁ =>
    by_cases h : i + 1 < k+1
    · exact ((hs.2 i (k+1) (by omega) (by omega) (by omega)).mul_right
        (ih₁ (by omega) h)).mul_right (hs.2 i (k+1) (by omega) (by omega) (by omega))
    · have he : i = k := by omega
      subst i
      exact braid_loop_step (hs.1 k (by omega))
        (commute_braidLoop (fun j hj => (hs.2 j (k+1) (by omega) (by omega) (by omega)).symm))

lemma braidLoops_commute {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ m) : Commute (braidLoop s j) (braidLoop s k) := by
  rcases lt_or_eq_of_le hjk with hlt | rfl
  · exact (commute_braidLoop (fun i hi => (braidLoop_commute hs hk (by omega)).symm)).symm
  · exact Commute.refl _

lemma braid_center_step {s L : G} (hc : Commute L (s*L*s)) :
    Commute s (L*(s*L*s)) := by
  change L*(s*L*s) = (s*L*s)*L at hc
  change s * (L * (s*L*s)) = L * (s*L*s) * s
  calc
    s * (L * (s*L*s)) = ((s*L*s)*L)*s := by group
    _ = (L*(s*L*s))*s := by rw [← hc]

lemma braidCenter_commute {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n i : ℕ} (hn : n ≤ m) (hi : i < n) : Commute (s i) (braidCenter s n) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one =>
    have he : i = 0 := by omega
    subst i
    simp only [braidCenter, braidLoop, mul_one, one_mul]
    exact (Commute.refl _).mul_right (Commute.refl _)
  | more k ih₀ ih₁ =>
    by_cases h : i < k+1
    · exact (ih₁ (by omega) h).mul_right (braidLoop_commute hs hn (by omega))
    · have he : i = k+1 := by omega
      subst i
      have hpre : Commute (s (k+1)) (braidCenter s k) :=
        commute_braidCenter (fun j hj => (hs.2 j (k+1) (by omega) (by omega) (by omega)).symm)
      have hlast := braid_center_step (braidLoops_commute hs (j := k+1) (k := k+2) (by omega) hn)
      simpa only [braidCenter, braidLoop, mul_assoc] using hpre.mul_right hlast

lemma braidDelta_shift {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n i : ℕ} (hn : n ≤ m) (hi : i + 1 < n) :
    braidDelta s n * s i = s (i+1) * braidDelta s n := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more k ih₀ ih₁ =>
    by_cases h : i+1 < k+1
    · rw [braidDelta, mul_assoc, ← (hs.2 i (k+1) (by omega) (by omega) (by omega)).eq,
        ← mul_assoc, ih₁ (by omega) h, mul_assoc]
    · have he : i = k := by omega
      subst i
      have hc : Commute (s (k+1)) (braidDelta s k) :=
        commute_braidDelta (fun j hj => (hs.2 j (k+1) (by omega) (by omega) (by omega)).symm)
      simp only [braidDelta]
      calc
        braidDelta s k * s k * s (k+1) * s k = braidDelta s k * (s k*s (k+1)*s k) := by group
        _ = braidDelta s k * (s (k+1)*s k*s (k+1)) := by rw [hs.1 k (by omega)]
        _ = (braidDelta s k * s (k+1)) * s k * s (k+1) := by group
        _ = (s (k+1) * braidDelta s k) * s k * s (k+1) := by rw [hc.symm.eq]
        _ = s (k+1) * (braidDelta s k * s k * s (k+1)) := by group

lemma braidDelta_conjugate {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {i : ℕ} (hi : i + 1 < m) :
    braidDelta s m * s i * (braidDelta s m)⁻¹ = s (i+1) := by
  rw [braidDelta_shift hs (le_refl m) hi]
  group

lemma braid_conjugate {a b : G} (h : a*b*a = b*a*b) : (a*b)*a*(a*b)⁻¹ = b := by
  rw [h]
  group

lemma braidCenter_two {s : ℕ → G} (h : s 0*s 1*s 0 = s 1*s 0*s 1) :
    braidCenter s 2 = (s 0*s 1)^3 := by
  simp only [braidCenter, braidLoop, mul_one, one_mul]
  calc
    s 0*s 0*(s 1*(s 0*s 0)*s 1) = s 0*(s 0*s 1*s 0)*s 0*s 1 := by group
    _ = s 0*(s 1*s 0*s 1)*s 0*s 1 := by rw [h]
    _ = (s 0*s 1)^3 := by simp only [pow_succ, pow_zero]; group

lemma braidLoop_congr {s t : ℕ → G} {n : ℕ} (he : ∀ i < n, s i = t i) :
    braidLoop s n = braidLoop t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [braidLoop, he n (by omega), ih (fun i hi => he i (by omega))]

lemma braidCenter_congr {s t : ℕ → G} {n : ℕ} (he : ∀ i < n, s i = t i) :
    braidCenter s n = braidCenter t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [braidCenter, braidLoop_congr he, ih (fun i hi => he i (by omega))]

lemma map_braidLoop {H : Type*} [Group H] (f : G →* H) (s : ℕ → G) (n : ℕ) :
    f (braidLoop s n) = braidLoop (fun i => f (s i)) n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [braidLoop, map_mul, ih]

lemma map_braidCenter {H : Type*} [Group H] (f : G →* H) (s : ℕ → G) (n : ℕ) :
    f (braidCenter s n) = braidCenter (fun i => f (s i)) n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [braidCenter, map_mul, map_braidLoop, ih]

lemma braidDelta_pow_conjugate {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {i k : ℕ} (hik : i+k < m) :
    (braidDelta s m)^k * s i * ((braidDelta s m)^k)⁻¹ = s (i+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (by omega)
    calc
      (braidDelta s m)^(k+1) * s i * ((braidDelta s m)^(k+1))⁻¹ =
        braidDelta s m * ((braidDelta s m)^k * s i * ((braidDelta s m)^k)⁻¹) *
          (braidDelta s m)⁻¹ := by rw [pow_succ']; group
      _ = braidDelta s m * s (i+k) * (braidDelta s m)⁻¹ := by rw [hi]
      _ = s (i+(k+1)) := by simpa only [Nat.add_assoc] using braidDelta_conjugate hs (by omega : i+k+1 < m)

lemma braidCenter_shift_conjugate {s : ℕ → G} {m : ℕ} (hs : BraidRelations m s)
    {n k : ℕ} (hnk : n+k ≤ m) :
    (braidDelta s m)^k * braidCenter s n * ((braidDelta s m)^k)⁻¹ =
      braidCenter (fun i => s (i+k)) n := by
  let f : G →* G := (MulAut.conj ((braidDelta s m)^k)).toMonoidHom
  change f (braidCenter s n) = _
  rw [map_braidCenter]
  apply braidCenter_congr
  intro i hi
  exact braidDelta_pow_conjugate hs (by omega)

end BraidAlgebra

section BraidLengths

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

lemma lengthPairing_braid_equal (hG : GeometricAction G X) (x : X)
    {g a b : G} (hga : Commute g a) (hgb : Commute g b) (hab : a*b*a = b*a*b) :
    lengthPairing x g a = lengthPairing x g b := by
  have he : lengthPairing x g (a*b*a) = lengthPairing x g (b*a*b) := congrArg _ hab
  rw [lengthPairing_centralizer hG x (hga.mul_right hgb) hga,
    lengthPairing_centralizer hG x hga hgb,
    lengthPairing_centralizer hG x (hgb.mul_right hga) hgb,
    lengthPairing_centralizer hG x hgb hga] at he
  linarith

lemma lengthPairing_braid_constant (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {m n : ℕ} (hs : BraidRelations m s) (hn : n ≤ m)
    (hc : ∀ i < n, Commute g (s i)) {i : ℕ} (hi : i < n) :
    lengthPairing x g (s i) = lengthPairing x g (s 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← lengthPairing_braid_equal hG x (hc i (by omega)) (hc (i+1) hi) (hs.1 i (by omega))]
    exact ih (by omega)

lemma lengthPairing_braidLoop (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {n : ℕ} {α : ℝ}
    (hc : ∀ i < n, Commute g (s i)) (he : ∀ i < n, lengthPairing x g (s i) = α) :
    lengthPairing x g (braidLoop s n) = 2 * (n : ℝ) * α := by
  induction n with
  | zero => simp [braidLoop, lengthPairing_one hG.2.1]
  | succ n ih =>
    rw [braidLoop,
      lengthPairing_centralizer hG x ((hc n (by omega)).mul_right (commute_braidLoop (fun i hi => hc i (by omega))))
        (hc n (by omega)),
      lengthPairing_centralizer hG x (hc n (by omega)) (commute_braidLoop (fun i hi => hc i (by omega))),
      ih (fun i hi => hc i (by omega)) (fun i hi => he i (by omega)), he n (by omega)]
    push_cast
    ring

lemma lengthPairing_braidCenter (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {n : ℕ} {α : ℝ}
    (hc : ∀ i < n, Commute g (s i)) (he : ∀ i < n, lengthPairing x g (s i) = α) :
    lengthPairing x g (braidCenter s n) = (n : ℝ) * (n+1) * α := by
  induction n with
  | zero => simp [braidCenter, lengthPairing_one hG.2.1]
  | succ n ih =>
    rw [braidCenter,
      lengthPairing_centralizer hG x (commute_braidCenter (fun i hi => hc i (by omega))) (commute_braidLoop hc),
      ih (fun i hi => hc i (by omega)) (fun i hi => he i (by omega)),
      lengthPairing_braidLoop hG x hc he]
    push_cast
    ring

lemma braidCenter_length_sq (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m n i : ℕ} (hs : BraidRelations m s) (hn : n ≤ m) (hi : i < n) :
    stableLengthAt x (braidCenter s n)^2 =
      (n : ℝ) * (n+1) * lengthPairing x (s i) (braidCenter s n) := by
  have hc : ∀ j < n, Commute (braidCenter s n) (s j) :=
    fun j hj => (braidCenter_commute hs hn hj).symm
  have he : ∀ j < n, lengthPairing x (braidCenter s n) (s j) =
      lengthPairing x (braidCenter s n) (s i) := by
    intro j hj
    rw [lengthPairing_braid_constant hG x hs hn hc hj,
      lengthPairing_braid_constant hG x hs hn hc hi]
  rw [← lengthPairing_self hG.2.1 x, lengthPairing_braidCenter hG x hc he,
    lengthPairing_symmetric x (hc i hi)]

omit [ProperSpace X] [Nonempty X] in
lemma braid_generator_length (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m i : ℕ} (hs : BraidRelations m s) (hi : i < m) :
    stableLengthAt x (s i) = stableLengthAt x (s 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← braid_conjugate (hs.1 i (by omega)), stableLength_conjugate hG.2.1]
    exact ih (by omega)

lemma braid_nonadjacent_pairing (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m i j : ℕ} (hs : BraidRelations m s)
    (hi : i < m) (hj : j < m) (hij : i+2 ≤ j) :
    lengthPairing x (s i) (s j) = lengthPairing x (s 0) (s 2) := by
  have he₁ : lengthPairing x (s i) (s j) = lengthPairing x (s 0) (s j) := by
    rw [lengthPairing_symmetric x (hs.2 i j hi hj hij),
      lengthPairing_braid_constant hG x hs (n := j-1) (by omega)
        (fun k hk => (hs.2 k j (by omega) hj (by omega)).symm) (by omega),
      lengthPairing_symmetric x (hs.2 0 j (by omega) hj (by omega)).symm]
  rw [he₁]
  have hj₂ : 2 ≤ j := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj₂
  clear he₁ hij hi hj₂
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2+(k+1) = (2+k)+1 by omega,
      ← lengthPairing_braid_equal hG x (hs.2 0 (2+k) (by omega) (by omega) (by omega))
        (hs.2 0 ((2+k)+1) (by omega) (by omega) (by omega)) (hs.1 (2+k) (by omega))]
    exact ih (by omega)

lemma lengthPairing_disjoint_centers (hG : GeometricAction G X) (x : X)
    {s t : ℕ → G} {n k : ℕ} {α : ℝ}
    (hc : ∀ i < n, ∀ j < k, Commute (s i) (t j))
    (he : ∀ i < n, ∀ j < k, lengthPairing x (s i) (t j) = α) :
    lengthPairing x (braidCenter s n) (braidCenter t k) =
      (n : ℝ)*(n+1)*((k : ℝ)*(k+1))*α := by
  have hct (i : ℕ) (hi : i < n) : Commute (s i) (braidCenter t k) :=
    commute_braidCenter (hc i hi)
  rw [lengthPairing_symmetric x (commute_braidCenter (fun i hi => (hct i hi).symm)).symm,
    lengthPairing_braidCenter hG x (fun i hi => (hct i hi).symm)
      (fun i hi => by rw [lengthPairing_symmetric x (hct i hi).symm,
        lengthPairing_braidCenter hG x (hc i hi) (he i hi)])]
  ring

lemma lengthPairing_braidDelta (hG : GeometricAction G X) (x : X)
    {g : G} {s : ℕ → G} {n : ℕ} {α : ℝ}
    (hc : ∀ i < n, Commute g (s i)) (he : ∀ i < n, lengthPairing x g (s i) = α) :
    lengthPairing x g (braidDelta s n) = (n : ℝ) * α := by
  induction n with
  | zero => simp [braidDelta, lengthPairing_one hG.2.1]
  | succ n ih =>
    rw [braidDelta,
      lengthPairing_centralizer hG x (commute_braidDelta (fun i hi => hc i (by omega))) (hc n (by omega)),
      ih (fun i hi => hc i (by omega)) (fun i hi => he i (by omega)), he n (by omega)]
    push_cast
    ring

lemma equiangular_product_sq (hG : GeometricAction G X) (x : X)
    {t : ℕ → G} {n : ℕ} {q v : ℝ}
    (hc : ∀ i j, i < j → j < n → Commute (t i) (t j))
    (hQ : ∀ i < n, stableLengthAt x (t i)^2 = q)
    (hP : ∀ i j, i < j → j < n → lengthPairing x (t i) (t j) = v) :
    stableLengthAt x (braidDelta t n)^2 = (n : ℝ)*q + (n : ℝ)*(n-1)*v := by
  induction n with
  | zero => simp [braidDelta, stableLength_one hG.2.1]
  | succ n ih =>
    rw [braidDelta, stableLength_product_sq,
      ih (fun i j hij hj => hc i j hij (by omega)) (fun i hi => hQ i (by omega))
        (fun i j hij hj => hP i j hij (by omega)), hQ n (by omega),
      lengthPairing_symmetric x (commute_braidDelta (fun i hi => (hc i n hi (by omega)).symm)).symm,
      lengthPairing_braidDelta hG x (fun i hi => (hc i n hi (by omega)).symm)
        (fun i hi => by rw [lengthPairing_symmetric x (hc i n hi (by omega)).symm, hP i n hi (by omega)])]
    push_cast
    ring

lemma braid_loop_character (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m n : ℕ} (hs : BraidRelations m s) (hn : n+2 ≤ m) :
    lengthPairing x (s 0) (braidLoop s (n+2)) =
      lengthPairing x (s 0) (braidLoop s 2) + 2*(n : ℝ)*lengthPairing x (s 0) (s 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, braidLoop,
      lengthPairing_centralizer hG x ((hs.2 0 (n+2) (by omega) (by omega) (by omega)).mul_right
        (braidLoop_commute hs (by omega) (by omega)))
        (hs.2 0 (n+2) (by omega) (by omega) (by omega)),
      lengthPairing_centralizer hG x (hs.2 0 (n+2) (by omega) (by omega) (by omega))
        (braidLoop_commute hs (by omega) (by omega)),
      ih (by omega), braid_nonadjacent_pairing hG x hs (by omega) (by omega) (by omega)]
    push_cast
    ring

lemma braid_center_character (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} {m n : ℕ} (hs : BraidRelations m s) (hn : n+2 ≤ m) :
    lengthPairing x (s 0) (braidCenter s (n+2)) =
      lengthPairing x (s 0) (braidCenter s 2) + (n : ℝ)*lengthPairing x (s 0) (braidLoop s 2) +
        (n : ℝ)*(n+1)*lengthPairing x (s 0) (s 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, braidCenter,
      lengthPairing_centralizer hG x (braidCenter_commute hs (by omega) (by omega))
        (braidLoop_commute hs (by omega) (by omega)),
      ih (by omega), braid_loop_character hG x hs (n := n+1) hn]
    push_cast
    ring

omit [ProperSpace X] [Nonempty X] in
lemma lengthPairing_le_self_of_equal_length (hG : GeometricAction G X) (x : X)
    {g h : G} (hc : Commute g h) (hL : stableLengthAt x g = stableLengthAt x h) :
    lengthPairing x g h ≤ stableLengthAt x g ^ 2 := by
  have he := stableLength_product_sq x g h⁻¹
  rw [stableLength_inv hG.2.1, ← hL, lengthPairing_inv hG.1 hG.2.1 x hc] at he
  nlinarith [sq_nonneg (stableLengthAt x (g*h⁻¹))]

/-- Quantitative braid constraint, in a division-free form. -/
lemma braid_forty_squared (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} (hs : BraidRelations 39 s) :
    143 * stableLengthAt x ((s 0)^2)^2 ≤ 57 * stableLengthAt x ((s 0*s 1)^3)^2 := by
  let q := stableLengthAt x (s 0)^2
  let v := lengthPairing x (s 0) (s 2)
  let β := lengthPairing x (s 0) (braidLoop s 2)
  have hodd : 0 ≤ 20*q + 380*v := by
    have he := equiangular_product_sq hG x (t := fun i => s (2*i)) (n := 20)
      (q := q) (v := v)
      (fun i j hij hj => hs.2 (2*i) (2*j) (by omega) (by omega) (by omega))
      (fun i hi => by dsimp [q]; rw [braid_generator_length hG x hs (by omega)])
      (fun i j hij hj => braid_nonadjacent_pairing hG x hs (by omega) (by omega) (by omega))
    norm_num at he
    rw [← he]
    positivity
  have hpc₂ : lengthPairing x (s 0) (braidCenter s 2) = 2*q + β := by
    change lengthPairing x (s 0) (braidCenter s 1 * braidLoop s 2) = _
    rw [lengthPairing_centralizer hG x (braidCenter_commute hs (by norm_num) (by norm_num))
      (braidLoop_commute hs (by norm_num) (by norm_num))]
    have he : braidCenter s 1 = (s 0)^2 := by simp [braidCenter, braidLoop, pow_two]
    rw [he, lengthPairing_pow_right hG.1 hG.2.1 x (Commute.refl _), lengthPairing_self hG.2.1]
    norm_num
    rfl
  have hQ₂ := braidCenter_length_sq hG x hs (n := 2) (i := 0) (by norm_num) (by norm_num)
  rw [hpc₂] at hQ₂
  norm_num at hQ₂
  have hpc₁₉ := braid_center_character hG x hs (n := 17) (by norm_num)
  rw [hpc₂] at hpc₁₉
  norm_num at hpc₁₉
  have hQ₁₉ := braidCenter_length_sq hG x hs (n := 19) (i := 0) (by norm_num) (by norm_num)
  rw [hpc₁₉] at hQ₁₉
  norm_num at hQ₁₉
  let t : ℕ → G := fun i => s (i+20)
  have hc (i : ℕ) (hi : i < 19) (j : ℕ) (hj : j < 19) : Commute (s i) (t j) :=
    hs.2 i (j+20) (by omega) (by omega) (by omega)
  have hP := lengthPairing_disjoint_centers hG x (n := 19) (k := 19) (α := v) hc
    (fun i hi j hj => braid_nonadjacent_pairing hG x hs (by omega) (by omega) (by omega))
  norm_num at hP
  have hc' : Commute (braidCenter s 19) (braidCenter t 19) :=
    (commute_braidCenter (fun i hi => (commute_braidCenter (hc i hi)).symm)).symm
  have hL : stableLengthAt x (braidCenter s 19) = stableLengthAt x (braidCenter t 19) := by
    rw [← braidCenter_shift_conjugate hs (by norm_num : 19+20 ≤ 39), stableLength_conjugate hG.2.1]
  have hbound := lengthPairing_le_self_of_equal_length hG x hc' hL
  rw [hP] at hbound
  have hraw : 572*q ≤ 57*stableLengthAt x (braidCenter s 2)^2 := by
    change stableLengthAt x (braidCenter s 19)^2 = 380*(2*q + β + 17*β + 306*v) at hQ₁₉
    linarith
  rw [braidCenter_two (hs.1 0 (by norm_num))] at hraw
  rw [stableLength_pow hG.2.1]
  norm_num
  dsimp [q] at hraw
  nlinarith

lemma braid_forty_ratio (hG : GeometricAction G X) (x : X)
    {s : ℕ → G} (hs : BraidRelations 39 s) (hD : 0 < stableLengthAt x ((s 0)^2)) :
    (stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)))^2 ≥ 143/513 ∧
    stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)) > 1/2 ∧
    stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)) =
      stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 1)^2)) := by
  have hsq := braid_forty_squared hG x hs
  have hbd : (stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)))^2 ≥ 143/513 := by
    rw [div_pow, ge_iff_le, le_div_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hD))]
    nlinarith
  refine ⟨hbd, ?_, ?_⟩
  · have hp : 0 ≤ stableLengthAt x ((s 0*s 1)^3) / (3*stableLengthAt x ((s 0)^2)) :=
      div_nonneg (stableLength_nonneg hG.2.1 x _) (by positivity)
    nlinarith
  · rw [stableLength_pow hG.2.1 x (s 1), braid_generator_length hG x hs (by norm_num),
      stableLength_pow hG.2.1 x (s 0)]

end BraidLengths

section TokenInvariant

abbrev SelectedPositions := {s : Finset ℕ // s.card ≤ 3}

def swapPositions (i : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.map (Equiv.swap i (i+1)).toEmbedding

@[simp] lemma mem_swapPositions (i k : ℕ) (s : Finset ℕ) :
    k ∈ swapPositions i s ↔ Equiv.swap i (i+1) k ∈ s := by
  simp [swapPositions]

@[simp] lemma card_swapPositions (i : ℕ) (s : Finset ℕ) :
    (swapPositions i s).card = s.card := Finset.card_map _

@[simp] lemma swapPositions_twice (i : ℕ) (s : Finset ℕ) :
    swapPositions i (swapPositions i s) = s := by
  ext k
  simp

def selectedPrefix (i : ℕ) (s : Finset ℕ) : ℕ := (s.filter (· < i)).card

lemma selectedPrefix_swap (i j : ℕ) (s : Finset ℕ) (hij : j ≠ i+1) :
    selectedPrefix j (swapPositions i s) = selectedPrefix j s := by
  have he : (swapPositions i s).filter (· < j) =
      swapPositions i (s.filter (· < j)) := by
    ext k
    simp only [Finset.mem_filter, mem_swapPositions]
    have hk : k < j ↔ Equiv.swap i (i+1) k < j := by
      rw [Equiv.swap_apply_def]
      split_ifs <;> omega
    exact and_congr_right (fun _ => hk)
  simp [selectedPrefix, he]

lemma selectedPrefix_succ (i : ℕ) (s : Finset ℕ) :
    selectedPrefix (i+1) s = selectedPrefix i s + if i ∈ s then 1 else 0 := by
  by_cases hi : i ∈ s
  · have he : s.filter (· < i+1) = insert i (s.filter (· < i)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro ⟨hk, hki⟩
        by_cases he : k = i
        · exact Or.inl he
        · exact Or.inr ⟨hk, by omega⟩
      · rintro (rfl | ⟨hk, hki⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hk, by omega⟩
    unfold selectedPrefix
    rw [he, Finset.card_insert_of_notMem (by simp)]
    simp [hi]
  · have he : s.filter (· < i+1) = s.filter (· < i) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨hk, hki⟩
        refine ⟨hk, ?_⟩
        by_contra hn
        have heq : k = i := by omega
        exact hi (heq ▸ hk)
      · intro ⟨hk, hki⟩
        exact ⟨hk, by omega⟩
    unfold selectedPrefix
    rw [he]
    simp [hi]

lemma selectedPrefix_zero_of_three (s : SelectedPositions) (i : ℕ)
    (h₀ : i ∈ s.val) (h₁ : i+1 ∈ s.val) (h₂ : i+2 ∈ s.val) :
    selectedPrefix i s.val = 0 := by
  have hc : ({i, i+1, i+2} : Finset ℕ).card = 3 := by
    simp
  have hsub : {i, i+1, i+2} ⊆ s.val := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> assumption
  have he : s.val = {i, i+1, i+2} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hc]; exact s.property)).symm
  simp [selectedPrefix, he]

lemma selected_not_four (s : SelectedPositions) (i j : ℕ) (hij : i+2 ≤ j)
    (hi : i ∈ s.val) (hi' : i+1 ∈ s.val) (hj : j ∈ s.val) : j+1 ∉ s.val := by
  intro hj'
  have hc : ({i, i+1, j, j+1} : Finset ℕ).card = 4 := by
    simp [show i ≠ j by omega, show i ≠ j+1 by omega, show i+1 ≠ j by omega]
  have hsub : {i, i+1, j, j+1} ⊆ s.val := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  have := s.property
  omega

lemma swapPositions_distant (i j : ℕ) (s : Finset ℕ) (hij : i+2 ≤ j) :
    swapPositions i (swapPositions j s) = swapPositions j (swapPositions i s) := by
  ext k
  simp only [mem_swapPositions]
  by_cases h₀ : k = i
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show i ≠ j by omega, show i ≠ j+1 by omega,
      show i+1 ≠ j by omega]
  by_cases h₁ : k = i+1
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show i ≠ j by omega, show i ≠ j+1 by omega,
      show i+1 ≠ j by omega]
  by_cases h₂ : k = j
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show j ≠ i by omega, show j ≠ i+1 by omega,
      show j+1 ≠ i by omega]
  by_cases h₃ : k = j+1
  · subst k
    simp [Equiv.swap_apply_of_ne_of_ne, show j ≠ i by omega, show j ≠ i+1 by omega,
      show j+1 ≠ i by omega]
  simp [Equiv.swap_apply_of_ne_of_ne, h₀, h₁, h₂, h₃]

lemma swapPositions_braid (i : ℕ) (s : Finset ℕ) :
    swapPositions i (swapPositions (i+1) (swapPositions i s)) =
      swapPositions (i+1) (swapPositions i (swapPositions (i+1) s)) := by
  ext k
  simp only [mem_swapPositions]
  by_cases h₀ : k = i
  · subst k
    simp [Equiv.swap_apply_def, Nat.add_assoc]
  by_cases h₁ : k = i+1
  · subst k
    simp [Equiv.swap_apply_def, Nat.add_assoc]
  by_cases h₂ : k = i+2
  · subst k
    simp [Equiv.swap_apply_def, Nat.add_assoc]
  simp [Equiv.swap_apply_def, h₀, h₁, h₂, Nat.add_assoc]

variable {H : Type*} [Group H]

def tokenRecord (u v : H) (i : ℕ) (s : Finset ℕ) : H :=
  if i ∈ s ∧ i+1 ∈ s then (if selectedPrefix i s = 0 then u else v) else 1

@[simp] lemma tokenRecord_swap (u v : H) (i : ℕ) (s : Finset ℕ) :
    tokenRecord u v i (swapPositions i s) = tokenRecord u v i s := by
  simp only [tokenRecord, mem_swapPositions, Equiv.swap_apply_left, Equiv.swap_apply_right,
    selectedPrefix_swap i i s (by omega)]
  simp only [and_comm]

abbrev TokenState (H : Type*) := SelectedPositions × H

def tokenPerm (u v : H) (i : ℕ) : Equiv.Perm (TokenState H) where
  toFun p := (⟨swapPositions i p.1.val, by simpa using p.1.property⟩,
    tokenRecord u v i p.1.val * p.2)
  invFun p := (⟨swapPositions i p.1.val, by simpa using p.1.property⟩,
    (tokenRecord u v i p.1.val)⁻¹ * p.2)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp

lemma tokenRecord_distant (u v : H) (i j : ℕ) (s : Finset ℕ) (hij : i+2 ≤ j) :
    tokenRecord u v i (swapPositions j s) = tokenRecord u v i s ∧
    tokenRecord u v j (swapPositions i s) = tokenRecord u v j s := by
  constructor
  · simp only [tokenRecord, mem_swapPositions,
      Equiv.swap_apply_of_ne_of_ne (by omega : i ≠ j) (by omega : i ≠ j+1),
      Equiv.swap_apply_of_ne_of_ne (by omega : i+1 ≠ j) (by omega : i+1 ≠ j+1),
      selectedPrefix_swap j i s (by omega)]
  · simp only [tokenRecord, mem_swapPositions,
      Equiv.swap_apply_of_ne_of_ne (by omega : j ≠ i) (by omega : j ≠ i+1),
      Equiv.swap_apply_of_ne_of_ne (by omega : j+1 ≠ i) (by omega : j+1 ≠ i+1),
      selectedPrefix_swap i j s (by omega)]

lemma tokenPerm_distant (u v : H) (i j : ℕ) (hij : i+2 ≤ j) :
    Commute (tokenPerm u v i) (tokenPerm u v j) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · apply Subtype.ext
    exact swapPositions_distant i j p.1.val hij
  · change tokenRecord u v i (swapPositions j p.1.val) *
        (tokenRecord u v j p.1.val * p.2) =
      tokenRecord u v j (swapPositions i p.1.val) *
        (tokenRecord u v i p.1.val * p.2)
    rw [(tokenRecord_distant u v i j p.1.val hij).1,
      (tokenRecord_distant u v i j p.1.val hij).2]
    by_cases hi : i ∈ p.1.val ∧ i+1 ∈ p.1.val
    · have hnj : ¬(j ∈ p.1.val ∧ j+1 ∈ p.1.val) :=
        fun hj => selected_not_four p.1 i j hij hi.1 hi.2 hj.1 hj.2
      simp [tokenRecord, hnj]
    · simp [tokenRecord, hi]

lemma tokenPerm_braid (u v : H) (h : u*v*u = v*u*v) (i : ℕ) :
    tokenPerm u v i * tokenPerm u v (i+1) * tokenPerm u v i =
      tokenPerm u v (i+1) * tokenPerm u v i * tokenPerm u v (i+1) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · apply Subtype.ext
    exact swapPositions_braid i p.1.val
  · change tokenRecord u v i (swapPositions (i+1) (swapPositions i p.1.val)) *
        (tokenRecord u v (i+1) (swapPositions i p.1.val) *
          (tokenRecord u v i p.1.val * p.2)) =
      tokenRecord u v (i+1) (swapPositions i (swapPositions (i+1) p.1.val)) *
        (tokenRecord u v i (swapPositions (i+1) p.1.val) *
          (tokenRecord u v (i+1) p.1.val * p.2))
    have hp₀ (s : Finset ℕ) := selectedPrefix_swap i i s (by omega)
    have hp₁ (s : Finset ℕ) := selectedPrefix_swap (i+1) i s (by omega)
    have hz : i ∈ p.1.val → i+1 ∈ p.1.val → i+2 ∈ p.1.val →
        selectedPrefix i p.1.val = 0 := selectedPrefix_zero_of_three p.1 i
    by_cases h₀ : i ∈ p.1.val <;> by_cases h₁ : i+1 ∈ p.1.val <;>
      by_cases h₂ : i+2 ∈ p.1.val <;>
      simp_all [tokenRecord, selectedPrefix_succ, mem_swapPositions,
        Equiv.swap_apply_def, Nat.add_assoc, ← mul_assoc]

end TokenInvariant

end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

section Presentations

variable {S H : Type*} [Group H]

lemma lift_alternating_constant (c : H) (s t : S) (n : ℕ) :
    FreeGroup.lift (fun _ : S => c) (alternating s t n) = c^n := by
  induction n generalizing s t with
  | zero => simp [alternating]
  | succ n ih => simp [alternating, ih, pow_succ']

/-- Exponent sum, valid for every Artin matrix (including infinity labels). -/
def artinExponent (M : S → S → Label) : ArtinGroup M →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := fun _ : S => Multiplicative.ofAdd (1 : ℤ)) (by
    rintro r ⟨s, t, n, _, rfl⟩
    simp only [map_mul, map_inv, lift_alternating_constant, mul_inv_cancel])

@[simp] lemma artinExponent_of (M : S → S → Label) (s : S) :
    artinExponent M (PresentedGroup.of s) = Multiplicative.ofAdd (1 : ℤ) :=
  PresentedGroup.toGroup.of _

lemma artin_generator_infinite_order (M : S → S → Label) (s : S) :
    ¬ IsOfFinOrder (PresentedGroup.of (rels := artinRelators M) s) := by
  intro hf
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hh := congrArg (artinExponent M) he
  have hz : (n : ℤ) = 0 := by
    simpa using congrArg Multiplicative.toAdd hh
  exact (Nat.ne_of_gt hn) (Int.natCast_eq_zero.mp hz)

/-- Positive braid presentation on n generators, i.e. the group B_(n+1). -/
def braidRelators (n : ℕ) : Set (FreeGroup (Fin n)) :=
  {w | ∃ (i : ℕ) (hi : i+1 < n),
    w = (FreeGroup.of ⟨i, by omega⟩ * FreeGroup.of ⟨i+1, hi⟩ * FreeGroup.of ⟨i, by omega⟩) *
      (FreeGroup.of ⟨i+1, hi⟩ * FreeGroup.of ⟨i, by omega⟩ * FreeGroup.of ⟨i+1, hi⟩)⁻¹} ∪
  {w | ∃ (i j : Fin n), i.val+2 ≤ j.val ∧
    w = (FreeGroup.of i * FreeGroup.of j) * (FreeGroup.of j * FreeGroup.of i)⁻¹}

abbrev BraidGroup (n : ℕ) := PresentedGroup (braidRelators n)

def braidGen (n i : ℕ) : BraidGroup n :=
  if hi : i < n then PresentedGroup.of ⟨i, hi⟩ else 1

lemma braidGroup_relation (n i : ℕ) (hi : i+1 < n) :
    braidGen n i * braidGen n (i+1) * braidGen n i =
      braidGen n (i+1) * braidGen n i * braidGen n (i+1) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := braidRelators n)
    (Or.inl ⟨i, hi, rfl⟩)
  simpa [braidGen, show i < n by omega, hi, PresentedGroup.of, map_mul] using h

lemma braidGroup_commute (n i j : ℕ) (hij : i+2 ≤ j) (hj : j < n) :
    Commute (braidGen n i) (braidGen n j) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := braidRelators n)
    (Or.inr ⟨⟨i, by omega⟩, ⟨j, hj⟩, hij, rfl⟩)
  change _ * _ = _ * _
  simpa [braidGen, show i < n by omega, hj, PresentedGroup.of, map_mul] using h

lemma braidGroup_relations (n : ℕ) : BraidRelations n (braidGen n) :=
  ⟨fun i hi => braidGroup_relation n i (by omega), fun i j _ hj hij =>
    braidGroup_commute n i j hij hj⟩

/-- Universal property, with equations rather than escaped relator words. -/
def braidLift {n : ℕ} (s : Fin n → H)
    (hb : ∀ (i : ℕ) (hi : i+1 < n),
      s ⟨i, by omega⟩ * s ⟨i+1, hi⟩ * s ⟨i, by omega⟩ =
        s ⟨i+1, hi⟩ * s ⟨i, by omega⟩ * s ⟨i+1, hi⟩)
    (hc : ∀ i j : Fin n, i.val+2 ≤ j.val → Commute (s i) (s j)) : BraidGroup n →* H :=
  PresentedGroup.toGroup (f := s) (by
    rintro r (⟨i, hi, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] using hb i hi
    · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] using (hc i j hij).eq)

@[simp] lemma braidLift_of {n : ℕ} (s : Fin n → H) (hb hc) (i : Fin n) :
    braidLift s hb hc (PresentedGroup.of i) = s i := PresentedGroup.toGroup.of _

@[simp] lemma braidLift_gen {n : ℕ} (s : Fin n → H) (hb hc) (i : ℕ) (hi : i < n) :
    braidLift s hb hc (braidGen n i) = s ⟨i, hi⟩ := by simp [braidGen, hi]

/-- Token representation. Unlike naive strand deletion, it is defined on every
selected-position state, so respects arbitrary signed prefixes and suffixes. -/
def braidTokenRepresentation (n : ℕ) : BraidGroup n →* Equiv.Perm (TokenState (BraidGroup 2)) :=
  braidLift (fun i => tokenPerm (braidGen 2 0) (braidGen 2 1) i.val)
    (fun i _ => tokenPerm_braid _ _ (braidGroup_relation 2 0 (by omega)) i)
    (fun i j hij => tokenPerm_distant _ _ i.val j.val hij)

def initialSelected : SelectedPositions := ⟨{0, 1, 2}, by decide⟩

lemma tokenPerm_initial (i : Fin 2) (q : BraidGroup 2) :
    tokenPerm (braidGen 2 0) (braidGen 2 1) i.val (initialSelected, q) =
      (initialSelected, PresentedGroup.of i * q) := by
  fin_cases i <;> apply Prod.ext
  all_goals simp [tokenPerm, initialSelected, tokenRecord, swapPositions, selectedPrefix, braidGen,
    Equiv.swap_apply_def, Finset.insert_comm] <;> decide

lemma braidTokenRepresentation_initial (g q : BraidGroup 2) :
    braidTokenRepresentation 2 g (initialSelected, q) = (initialSelected, g*q) := by
  let K : Subgroup (BraidGroup 2) :=
    { carrier := {g | ∀ q, braidTokenRepresentation 2 g (initialSelected, q) =
        (initialSelected, g*q)}
      one_mem' := by intro q; simp
      mul_mem' := by
        intro g h hg hh q
        change ∀ t, braidTokenRepresentation 2 g (initialSelected, t) = _ at hg
        change ∀ t, braidTokenRepresentation 2 h (initialSelected, t) = _ at hh
        simp only [map_mul, Equiv.Perm.mul_apply, hh, hg, mul_assoc]
      inv_mem' := by
        intro g hg q
        apply (braidTokenRepresentation 2 g).injective
        change ∀ t, braidTokenRepresentation 2 g (initialSelected, t) = _ at hg
        simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply, hg, mul_inv_cancel_left] }
  exact PresentedGroup.generated_by (braidRelators 2) K
    (fun i q => by simpa [braidTokenRepresentation] using tokenPerm_initial i q) g q

lemma braidTokenRepresentation_two_injective : Function.Injective (braidTokenRepresentation 2) := by
  intro g h he
  have hh := congrArg (fun f : Equiv.Perm (TokenState (BraidGroup 2)) => f (initialSelected, 1)) he
  simpa [braidTokenRepresentation_initial] using congrArg Prod.snd hh

/-- Initial B3 inclusion in every B_(n+1), for n≥2. -/
def initialBraidInclusion (n : ℕ) (hn : 2 ≤ n) : BraidGroup 2 →* BraidGroup n :=
  braidLift (fun i => braidGen n i.val)
    (fun i hi => braidGroup_relation n i (by omega))
    (fun i j hij => by omega)

lemma initialBraidInclusion_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (initialBraidInclusion n hn) := by
  have he : (braidTokenRepresentation n).comp (initialBraidInclusion n hn) =
      braidTokenRepresentation 2 := by
    apply PresentedGroup.ext
    intro i
    simp [initialBraidInclusion, braidTokenRepresentation, braidGen, show i.val < n by omega]
  apply Function.Injective.of_comp (f := braidTokenRepresentation n)
  rw [← MonoidHom.coe_comp, he]
  exact braidTokenRepresentation_two_injective

end Presentations

section TrianglePresentation

def triangleRelators : Set (FreeGroup (Fin 3)) :=
  {w | ∃ i : Fin 3,
    w = (FreeGroup.of i * FreeGroup.of (i+1) * FreeGroup.of i) *
      (FreeGroup.of (i+1) * FreeGroup.of i * FreeGroup.of (i+1))⁻¹}

abbrev TriangleGroup := PresentedGroup triangleRelators

def triangleGen (i : Fin 3) : TriangleGroup := PresentedGroup.of i

lemma triangle_braid (i : Fin 3) :
    triangleGen i * triangleGen (i+1) * triangleGen i =
      triangleGen (i+1) * triangleGen i * triangleGen (i+1) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := triangleRelators) ⟨i, rfl⟩
  simpa [triangleGen, PresentedGroup.of, map_mul] using h

def triangleLift {H : Type*} [Group H] (s : Fin 3 → H)
    (hb : ∀ i : Fin 3, s i * s (i+1) * s i = s (i+1) * s i * s (i+1)) :
    TriangleGroup →* H :=
  PresentedGroup.toGroup (f := s) (by
    rintro r ⟨i, rfl⟩
    simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one] using hb i)

@[simp] lemma triangleLift_gen {H : Type*} [Group H] (s : Fin 3 → H) (hb) (i : Fin 3) :
    triangleLift s hb (triangleGen i) = s i := PresentedGroup.toGroup.of _

def trianglePair (i : Fin 3) : BraidGroup 2 →* TriangleGroup :=
  braidLift (fun j => if j.val = 0 then triangleGen i else triangleGen (i+1))
    (fun j hj => by
      have : j = 0 := by omega
      subst j
      simpa using triangle_braid i)
    (fun j k h => by omega)

def trianglePairRetraction (i : Fin 3) : TriangleGroup →* BraidGroup 2 :=
  triangleLift (fun j => if j = i+1 then braidGen 2 1 else braidGen 2 0) (by
    have hb := braidGroup_relation 2 0 (by omega)
    intro j
    fin_cases i <;> fin_cases j <;> simp_all)

lemma trianglePair_leftInverse (i : Fin 3) :
    (trianglePairRetraction i).comp (trianglePair i) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro j
  fin_cases j <;> fin_cases i <;>
    simp [trianglePair, trianglePairRetraction, braidGen]

lemma trianglePair_injective (i : Fin 3) : Function.Injective (trianglePair i) := by
  apply Function.Injective.of_comp (f := trianglePairRetraction i)
  rw [← MonoidHom.coe_comp, trianglePair_leftInverse]
  exact Function.injective_id

def triangleExponent : TriangleGroup →* Multiplicative ℤ :=
  triangleLift (fun _ => Multiplicative.ofAdd (1 : ℤ)) (by intro i; rfl)

@[simp] lemma triangleExponent_gen (i : Fin 3) :
    triangleExponent (triangleGen i) = Multiplicative.ofAdd (1 : ℤ) := triangleLift_gen _ _ _

lemma triangle_generator_infinite_order (i : Fin 3) : ¬ IsOfFinOrder (triangleGen i) := by
  intro hf
  obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hh := congrArg triangleExponent he
  have hz : (n : ℤ) = 0 := by simpa using congrArg Multiplicative.toAdd hh
  exact (Nat.ne_of_gt hn) (Int.natCast_eq_zero.mp hz)

def triangleX (b i : Fin 3) : TriangleGroup :=
  if i = 0 then triangleGen b else if i = 1 then triangleGen (b+1)
  else (triangleGen (b+1))⁻¹ * triangleGen b * triangleGen (b+1)

def triangleH (b : Fin 3) : TriangleGroup := triangleGen b * triangleGen (b+1)

lemma triangular_relation (b i : Fin 3) : triangleX b i * triangleX b (i+1) = triangleH b := by
  fin_cases i
  · simp [triangleX, triangleH]
  · simp [triangleX, triangleH, mul_assoc]
  · simp only [triangleX]
    unfold triangleH
    have hb := triangle_braid b
    calc
      (triangleGen (b+1))⁻¹ * triangleGen b * triangleGen (b+1) * triangleGen b =
          (triangleGen (b+1))⁻¹ * (triangleGen b * triangleGen (b+1) * triangleGen b) := by group
      _ = _ := by rw [hb]; group

@[simp] lemma triangleExponent_X (b i : Fin 3) :
    triangleExponent (triangleX b i) = Multiplicative.ofAdd (1 : ℤ) := by
  fin_cases i <;> simp [triangleX]

@[simp] lemma triangleExponent_H (b : Fin 3) :
    triangleExponent (triangleH b) = Multiplicative.ofAdd (2 : ℤ) := by
  simp only [triangleH, map_mul, triangleExponent_gen]
  rfl

end TrianglePresentation

/-- Signed edge directions in the nine-letter triangular presentation.
Indices 0..8 are positive; indices 9..17 are negative. -/
abbrev LinkDirection := Fin 18

/-- The three theta graphs, glued at a±, b±, c±, with cell identities retained. -/
def linkNeighbors (d : LinkDirection) : Finset LinkDirection :=
  match d.val with
  | 0 => {6,12,8,11}
  | 1 => {6,9,7,13}
  | 2 => {7,10,8,14}
  | 3 => {6,10}
  | 4 => {7,11}
  | 5 => {8,9}
  | 6 => {0,1,3}
  | 7 => {1,2,4}
  | 8 => {2,0,5}
  | 9 => {1,15,5,17}
  | 10 => {3,15,2,16}
  | 11 => {4,16,0,17}
  | 12 => {0,15}
  | 13 => {1,16}
  | 14 => {2,17}
  | 15 => {10,12,9}
  | 16 => {11,13,10}
  | _ => {9,14,11}

lemma linkNeighbors_symm : ∀ p q : LinkDirection, p ∈ linkNeighbors q ↔ q ∈ linkNeighbors p := by
  decide

lemma linkNeighbors_irrefl : ∀ p : LinkDirection, p ∉ linkNeighbors p := by decide

/-- Endpoints of nonbacktracking walks with a prescribed first oriented edge. -/
def linkEnds : ℕ → LinkDirection → LinkDirection → Finset LinkDirection
  | 0, _, q => {q}
  | n+1, p, q => ((linkNeighbors q).erase p).biUnion (fun r => linkEnds n q r)

lemma link_girth0 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 0 p q := by decide
lemma link_girth1 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 1 p q := by decide
lemma link_girth2 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 2 p q := by decide
lemma link_girth3 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 3 p q := by decide
lemma link_girth4 : ∀ p q : LinkDirection, q ∈ linkNeighbors p → p ∉ linkEnds 4 p q := by decide

lemma link_girth (n : ℕ) (hn : n < 5) (p q : LinkDirection) (h : q ∈ linkNeighbors p) :
    p ∉ linkEnds n p q := by
  interval_cases n
  · exact link_girth0 p q h
  · exact link_girth1 p q h
  · exact link_girth2 p q h
  · exact link_girth3 p q h
  · exact link_girth4 p q h

lemma mem_linkEnds_of_path (n : ℕ) (v : ℕ → LinkDirection)
    (hadj : ∀ i < n+1, v (i+1) ∈ linkNeighbors (v i))
    (hnob : ∀ i < n, v (i+2) ≠ v i) :
    v (n+1) ∈ linkEnds n (v 0) (v 1) := by
  induction n generalizing v with
  | zero => simp [linkEnds]
  | succ n ih =>
    simp only [linkEnds, Finset.mem_biUnion, Finset.mem_erase]
    refine ⟨v 2, ⟨hnob 0 (by omega), hadj 1 (by omega)⟩, ?_⟩
    simpa [Nat.add_assoc] using ih (fun i => v (i+1))
      (fun i hi => hadj (i+1) (by omega)) (fun i hi => hnob (i+1) (by omega))

/-- Every nonempty closed nonbacktracking walk in the exact link has at least six edges. -/
lemma link_closed_walk_length (n : ℕ) (hn : 0 < n) (v : ℕ → LinkDirection)
    (hadj : ∀ i < n, v (i+1) ∈ linkNeighbors (v i))
    (hnob : ∀ i, i+2 ≤ n → v (i+2) ≠ v i) (hclosed : v n = v 0) : 6 ≤ n := by
  by_contra h
  have he := mem_linkEnds_of_path (n-1) v (by simpa [Nat.sub_add_cancel hn] using hadj)
    (fun i hi => hnob i (by omega))
  rw [Nat.sub_add_cancel hn, hclosed] at he
  exact link_girth (n-1) (by omega) (v 0) (v 1) (hadj 0 hn) he

end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

/-- Oriented finite triangular incidence data. Faces/edges may have repeated
incidences; no topological assumption is built into this record. -/
structure TriangleMesh (F V : Type*) where
  mate : Equiv.Perm (F × Fin 3)
  mate_involutive : Function.Involutive mate
  mate_ne : ∀ d, mate d ≠ d
  tail : F × Fin 3 → V
  tail_mate : ∀ d, tail (mate d) = tail (d.1, d.2+1)

namespace TriangleMesh
variable {F V : Type*} (M : TriangleMesh F V)

abbrev Dart := F × Fin 3

def rotate : Equiv.Perm (Dart (F := F)) where
  toFun d := (d.1,d.2+1)
  invFun d := (d.1,d.2-1)
  left_inv d := by ext <;> simp
  right_inv d := by ext <;> simp

@[simp] lemma rotate_apply (d : Dart (F := F)) : rotate d = (d.1,d.2+1) := rfl
@[simp] lemma rotate_symm_apply (d : Dart (F := F)) : rotate.symm d = (d.1,d.2-1) := rfl

@[simp] lemma mate_mate (d : Dart (F := F)) : M.mate (M.mate d) = d := M.mate_involutive d

lemma tail_rotate_mate (d : Dart (F := F)) : M.tail (rotate (M.mate d)) = M.tail d := by
  rw [rotate_apply, ← M.tail_mate, M.mate_mate]

def turn : Equiv.Perm (Dart (F := F)) := M.mate * rotate.symm

@[simp] lemma turn_apply (d : Dart (F := F)) : M.turn d = M.mate (rotate.symm d) := rfl

@[simp] lemma tail_turn (d : Dart (F := F)) : M.tail (M.turn d) = M.tail d := by
  rw [turn_apply, M.tail_mate]
  simp

/-- A real edge cocycle is exact. This algebraic formulation allows the
fold-deletion proof to avoid any appeal to an unformalized planar theorem. -/
def Exact : Prop :=
  ∀ w : Dart (F := F) → ℝ,
    (∀ d, w (M.mate d) = -w d) →
    (∀ f, ∑ i : Fin 3, w (f,i) = 0) →
    ∃ p : V → ℝ, ∀ d, w d = p (M.tail (rotate d)) - p (M.tail d)

section OrientedEdges
variable [LinearOrder (Dart (F := F))]

abbrev Edge := {d : Dart (F := F) // d < M.mate d}

noncomputable def edgeRep (d : Dart (F := F)) : M.Edge :=
  if h : d < M.mate d then ⟨d,h⟩ else
    ⟨M.mate d, by rw [M.mate_mate]; exact lt_of_le_of_ne (le_of_not_gt h) (M.mate_ne d)⟩

lemma edgeRep_mate (d : Dart (F := F)) : M.edgeRep (M.mate d) = M.edgeRep d := by
  apply Subtype.ext
  unfold edgeRep
  by_cases h : d < M.mate d
  · simp [h, not_lt_of_gt h]
  · have h' : M.mate d < d := lt_of_le_of_ne (le_of_not_gt h) (M.mate_ne d)
    simp [h, h']

@[simp] lemma edgeRep_edge (e : M.Edge) : M.edgeRep e.val = e := by
  apply Subtype.ext
  simp [edgeRep, e.property]

noncomputable def extend (w : M.Edge → ℝ) (d : Dart (F := F)) : ℝ :=
  if d < M.mate d then w (M.edgeRep d) else -w (M.edgeRep d)

@[simp] lemma extend_edge (w : M.Edge → ℝ) (e : M.Edge) : M.extend w e.val = w e := by
  simp [extend, e.property]

lemma extend_mate (w : M.Edge → ℝ) (d : Dart (F := F)) : M.extend w (M.mate d) = -M.extend w d := by
  unfold extend
  rw [M.edgeRep_mate, M.mate_mate]
  by_cases h : d < M.mate d
  · simp [h, not_lt_of_gt h]
  · have h' : M.mate d < d := lt_of_le_of_ne (le_of_not_gt h) (M.mate_ne d)
    simp [h, h']

lemma extend_of_antisymmetric (w : Dart (F := F) → ℝ)
    (hw : ∀ d, w (M.mate d) = -w d) (d : Dart (F := F)) :
    M.extend (fun e => w e.val) d = w d := by
  unfold extend edgeRep
  split_ifs <;> simp_all

noncomputable def edgeDartEquiv : M.Edge × Bool ≃ Dart (F := F) where
  toFun p := if p.2 then M.mate p.1.val else p.1.val
  invFun d := (M.edgeRep d, decide (¬ d < M.mate d))
  left_inv p := by
    rcases p with ⟨e,b⟩
    cases b
    · simp [edgeRep, e.property]
    · have hn : ¬ M.mate e.val < e.val := not_lt_of_gt e.property
      simp [edgeRep, hn]
  right_inv d := by
    by_cases h : d < M.mate d
    · simp [h, edgeRep]
    · simp [h, edgeRep]

lemma edge_card [Fintype F] [Fintype M.Edge] : 2 * Fintype.card M.Edge = 3 * Fintype.card F := by
  have he := Fintype.card_congr M.edgeDartEquiv
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at he
  omega

noncomputable def coboundary : (V → ℝ) →ₗ[ℝ] (M.Edge → ℝ) where
  toFun p e := p (M.tail (rotate e.val)) - p (M.tail e.val)
  map_add' p q := by ext e; simp; ring
  map_smul' c p := by ext e; simp; ring

lemma extend_coboundary (p : V → ℝ) (d : Dart (F := F)) :
    M.extend (M.coboundary p) d = p (M.tail (rotate d)) - p (M.tail d) := by
  change M.extend (fun e => p (M.tail (rotate e.val)) - p (M.tail e.val)) d = _
  apply M.extend_of_antisymmetric (fun e => p (M.tail (rotate e)) - p (M.tail e))
  intro e
  rw [M.tail_rotate_mate, M.tail_mate, rotate_apply]
  ring

noncomputable def boundarySum : (M.Edge → ℝ) →ₗ[ℝ] (F → ℝ) where
  toFun w f := ∑ i : Fin 3, M.extend w (f,i)
  map_add' w z := by
    ext f
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold extend
    split_ifs <;> simp [add_comm]
  map_smul' c w := by
    ext f
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold extend
    split_ifs <;> simp

lemma boundarySum_coboundary (p : V → ℝ) : M.boundarySum (M.coboundary p) = 0 := by
  ext f
  change (∑ i : Fin 3, M.extend (M.coboundary p) (f,i)) = 0
  simp only [M.extend_coboundary, Fin.sum_univ_three, rotate_apply]
  change p (M.tail (f,1)) - p (M.tail (f,0)) +
    (p (M.tail (f,2)) - p (M.tail (f,1))) +
    (p (M.tail (f,0)) - p (M.tail (f,2))) = 0
  ring

lemma exact_iff : M.Exact ↔ M.boundarySum.ker = M.coboundary.range := by
  constructor
  · intro he
    apply le_antisymm
    · intro w hw
      rcases he (M.extend w) (M.extend_mate w) (congrFun hw) with ⟨p,hp⟩
      refine ⟨p, ?_⟩
      ext e
      change p (M.tail (rotate e.val)) - p (M.tail e.val) = w e
      simpa only [M.extend_edge] using (hp e.val).symm
    · rintro _ ⟨p,rfl⟩
      exact M.boundarySum_coboundary p
  · intro he w ha hf
    have hk : (fun e : M.Edge => w e.val) ∈ M.boundarySum.ker := by
      ext f
      change (∑ i : Fin 3, M.extend (fun e => w e.val) (f,i)) = 0
      simpa only [M.extend_of_antisymmetric w ha] using hf f
    rw [he] at hk
    rcases hk with ⟨p,hp⟩
    refine ⟨p, fun d => ?_⟩
    rw [← M.extend_of_antisymmetric w ha d, ← hp, M.extend_coboundary]

lemma sum_boundarySum [Fintype F] (w : M.Edge → ℝ) : ∑ f, M.boundarySum w f = 0 := by
  have h : (∑ d : Dart (F := F), M.extend w d) = -(∑ d : Dart (F := F), M.extend w d) := by
    calc
      _ = ∑ d : Dart (F := F), M.extend w (M.mate d) := (Equiv.sum_comp M.mate _).symm
      _ = _ := by simp [M.extend_mate]
  have hz : (∑ d : Dart (F := F), M.extend w d) = 0 := by linarith
  simpa only [boundarySum, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type] using hz

lemma exact_euler_inequality [Fintype F] [Fintype V] [Nonempty F] (he : M.Exact) :
    3 * Fintype.card F < 2 * (Fintype.card V + Fintype.card F) := by
  classical
  let : Fintype M.Edge := Fintype.ofFinite _
  have hproper : M.boundarySum.range ≠ ⊤ := by
    intro h
    have h1 : (fun _ : F => (1 : ℝ)) ∈ M.boundarySum.range := by rw [h]; trivial
    rcases h1 with ⟨w,hw⟩
    have hz := M.sum_boundarySum w
    rw [hw] at hz
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hz
    have hn := Fintype.card_pos (α := F)
    exact (Nat.ne_of_gt hn) (Nat.cast_eq_zero.mp hz)
  have hd := LinearMap.finrank_range_add_finrank_ker M.boundarySum
  have hr := Submodule.finrank_lt (K := ℝ) hproper
  have hk := LinearMap.finrank_range_le M.coboundary
  rw [← M.exact_iff.mp he] at hk
  simp only [Module.finrank_pi] at hd hr hk
  have hc := M.edge_card
  omega

end OrientedEdges

lemma tail_iterate_turn (d : Dart (F := F)) (n : ℕ) :
    M.tail (M.turn^[n] d) = M.tail d := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', M.tail_turn] using ih

lemma six_turns_injective (direction : Dart (F := F) → LinkDirection)
    (hadj : ∀ d, direction (M.turn d) ∈ linkNeighbors (direction d))
    (hnob : ∀ d, direction (M.turn (M.turn d)) ≠ direction d)
    (d : Dart (F := F)) :
    Function.Injective (fun i : Fin 6 => M.turn^[i.val] d) := by
  have hn (i j : Fin 6) (hij : i.val < j.val) : M.turn^[i.val] d ≠ M.turn^[j.val] d := by
    intro he
    let v : ℕ → LinkDirection := fun k => direction (M.turn^[k] (M.turn^[i.val] d))
    have ha : ∀ k < j.val-i.val, v (k+1) ∈ linkNeighbors (v k) := by
      intro k _
      simpa only [v, Function.iterate_succ_apply'] using hadj (M.turn^[k] (M.turn^[i.val] d))
    have hb : ∀ k, k+2 ≤ j.val-i.val → v (k+2) ≠ v k := by
      intro k _
      simpa only [v, Function.iterate_succ_apply'] using hnob (M.turn^[k] (M.turn^[i.val] d))
    have hv : v (j.val-i.val) = v 0 := by
      dsimp only [v, Function.iterate_zero, id_eq]
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hij), ← he]
    have hg := link_closed_walk_length (j.val-i.val) (by omega) v ha hb hv
    omega
  intro i j he
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (hn i j h he)
  · exact h
  · exact False.elim (hn j i h he.symm)

lemma degree_at_least_six [Fintype F] [Fintype V]
    (hs : Function.Surjective M.tail)
    (direction : Dart (F := F) → LinkDirection)
    (hadj : ∀ d, direction (M.turn d) ∈ linkNeighbors (direction d))
    (hnob : ∀ d, direction (M.turn (M.turn d)) ≠ direction d) :
    6 * Fintype.card V ≤ 3 * Fintype.card F := by
  classical
  have hb (v : V) : 6 ≤ Fintype.card {d // M.tail d = v} := by
    obtain ⟨d,hd⟩ := hs v
    let j : Fin 6 → {d // M.tail d = v} := fun i =>
      ⟨M.turn^[i.val] d, (M.tail_iterate_turn d i.val).trans hd⟩
    have hi : Function.Injective j := by
      intro a b hab
      exact M.six_turns_injective direction hadj hnob d (congrArg Subtype.val hab)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hi
  have he : (∑ v : V, Fintype.card {d // M.tail d = v}) = 3 * Fintype.card F := by
    have h := Fintype.sum_fiberwise M.tail (fun _ => (1 : ℕ))
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod, Fintype.card_fin, mul_comm, one_mul] using h
  have hh := Finset.sum_le_sum (fun (v : V) (_ : v ∈ Finset.univ) => hb v)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, he, mul_comm] using hh

/-- Curvature forces a backtrack in any nonempty exact triangular mesh.
Only finite linear algebra, incidence counting, and the checked finite link
are used here, in place of a black-box planar Euler theorem. -/
theorem exists_link_backtrack [Fintype F] [Fintype V] [Nonempty F]
    (he : M.Exact) (hs : Function.Surjective M.tail)
    (direction : Dart (F := F) → LinkDirection)
    (hadj : ∀ d, direction (M.turn d) ∈ linkNeighbors (direction d)) :
    ∃ d, direction (M.turn (M.turn d)) = direction d := by
  classical
  by_contra hn
  have hb : ∀ d, direction (M.turn (M.turn d)) ≠ direction d := by simpa using hn
  have hd := M.degree_at_least_six hs direction hadj hb
  let : LinearOrder (Dart (F := F)) := (Fintype.equivFin _).linearOrder
  have hi := M.exact_euler_inequality he
  omega

end TriangleMesh
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

section RestrictedGeometry

variable {X : Type*} [MetricSpace X]

def GeodesicallyConvex (C : Set X) : Prop :=
  ∀ (a b : X), a ∈ C → b ∈ C → ∀ γ : ℝ → X, Segment a b γ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ C

lemma CAT0_subtype (hX : CAT0 X) {C : Set X} (hC : GeodesicallyConvex C) : CAT0 C := by
  classical
  constructor
  · intro a b
    obtain ⟨γ, hγ⟩ := hX.1 a.val b.val
    let η : ℝ → C := fun t => if ht : t ∈ Set.Icc (0 : ℝ) 1
      then ⟨γ t, hC a b a.property b.property γ hγ t ht⟩ else a
    refine ⟨η, ?_, ?_, ?_⟩
    · apply Subtype.ext
      simp [η, hγ.1]
    · apply Subtype.ext
      simp [η, hγ.2.1]
    · intro s hs t ht
      change dist (η s).val (η t).val = |s-t| * dist a.val b.val
      simp only [η, dite_eq_left hs, dite_eq_left ht]
      exact hγ.2.2 s hs t ht
  · intro a b c γ η hγ hη t ht u hu
    have hg : Segment a.val b.val (fun s => (γ s).val) :=
      ⟨congrArg Subtype.val hγ.1, congrArg Subtype.val hγ.2.1, hγ.2.2⟩
    have he : Segment a.val c.val (fun s => (η s).val) :=
      ⟨congrArg Subtype.val hη.1, congrArg Subtype.val hη.2.1, hη.2.2⟩
    exact hX.2 a.val b.val c.val _ _ hg he t ht u hu

end RestrictedGeometry

section CommonCentralizerGeometry

variable {ι G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

def tupleCentralizer (q : ι → G) : Subgroup G where
  carrier := {g | ∀ i, Commute g (q i)}
  one_mem' := fun _ => Commute.one_left _
  mul_mem' := fun ha hb i => (ha i).mul_left (hb i)
  inv_mem' := fun ha i => (ha i).inv_left

def displacementSublevel (q : ι → G) (A : ℝ) : Set X :=
  {x | ∀ i, dist x (q i • x) ≤ A}

lemma displacementSublevel_closed (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) : IsClosed (displacementSublevel (X := X) q A) := by
  have he : displacementSublevel (X := X) q A = ⋂ i, {x | dist x (q i • x) ≤ A} := by
    ext x
    simp [displacementSublevel]
  rw [he]
  exact isClosed_iInter (fun i => isClosed_le (continuous_id.dist (hi (q i)).continuous) continuous_const)

lemma displacementSublevel_convex (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (q : ι → G) (A : ℝ) :
    GeodesicallyConvex (displacementSublevel (X := X) q A) := by
  intro a b ha hb γ hγ t ht i
  have hη := segment_isometry hγ (hi (q i))
  have hc := comparison_convexity hX hγ hη ht
  have hm₁ := mul_le_mul_of_nonneg_left (ha i) (show 0 ≤ 1-t by linarith [ht.2])
  have hm₂ := mul_le_mul_of_nonneg_left (hb i) ht.1
  change dist (γ t) (q i • γ t) ≤ A
  dsimp only [Function.comp_apply] at hc
  linarith

lemma displacementSublevel_smul (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) (g : tupleCentralizer q)
    {x : X} (hx : x ∈ displacementSublevel q A) :
    g.val • x ∈ displacementSublevel q A := by
  intro i
  have he : q i • (g.val • x) = g.val • (q i • x) := by
    simp only [← mul_smul, (g.property i).eq]
  rw [he, (hi g.val).dist_eq]
  exact hx i

@[instance_reducible] noncomputable def sublevelAction (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) : MulAction (tupleCentralizer q) (displacementSublevel (X := X) q A) where
  smul g x := ⟨g.val • x.val, displacementSublevel_smul hi q A g x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g.val h.val x.val)

lemma sublevelAction_isometry (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) :
    letI := sublevelAction hi q A
    ∀ g : tupleCentralizer q, Isometry (fun x : displacementSublevel (X := X) q A => g • x) := by
  let := sublevelAction hi q A
  intro g
  exact Isometry.of_dist_eq (fun x y => (hi g.val).dist_eq x.val y.val)

lemma sublevelAction_proper (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (hp : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite)
    (q : ι → G) (A : ℝ) :
    letI := sublevelAction hi q A
    ∀ K : Set (displacementSublevel (X := X) q A), IsCompact K →
      {g : tupleCentralizer q | ((fun x => g • x) '' K ∩ K).Nonempty}.Finite := by
  let := sublevelAction hi q A
  intro K hK
  have hF := (hp (Subtype.val '' K) (hK.image continuous_subtype_val)).preimage
    (f := ((↑) : tupleCentralizer q → G))
    (fun _ _ _ _ h => Subtype.val_injective h)
  apply hF.subset
  rintro g ⟨x, ⟨y, hy, rfl⟩, hx⟩
  exact ⟨g.val • y.val, ⟨y.val, ⟨y, hy, rfl⟩, rfl⟩, ⟨g • y, hx, rfl⟩⟩

lemma sublevelAction_cocompact [Finite ι] [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (q : ι → G) (A : ℝ) (hA : 0 ≤ A) :
    letI := sublevelAction hG.2.1 q A
    ∃ L : Set (displacementSublevel (X := X) q A), IsCompact L ∧
      ∀ x : displacementSublevel (X := X) q A,
        ∃ g : tupleCentralizer q, ∃ k ∈ L, g • k = x := by
  classical
  let := sublevelAction hG.2.1 q A
  let o : X := Classical.choice inferInstance
  obtain ⟨K, hK, hcover⟩ := hG.2.2.2
  let F : Set G := {g | ∃ p ∈ K, dist p (g • p) ≤ A}
  have hF : F.Finite := finite_movers_of_compact hG.2.2.1 hK o A hA
  let Q : Set (ι → G) := {v | (∀ i, v i ∈ F) ∧ ∃ g : G, ∀ i, g⁻¹ * q i * g = v i}
  have hQ : Q.Finite := (Set.Finite.pi (fun _ : ι => hF)).subset (by
    intro v hv i _
    exact hv.1 i)
  let : Finite Q := hQ.to_subtype
  let rep : Q → G := fun v => Classical.choose v.property.2
  have hrep (v : Q) (i : ι) : (rep v)⁻¹ * q i * rep v = v.val i :=
    Classical.choose_spec v.property.2 i
  let L₀ : Set X := ⋃ v : Q, (fun p => rep v • p) '' K
  have hL₀ : IsCompact L₀ := isCompact_iUnion (fun v => hK.image (hG.2.1 (rep v)).continuous)
  let L : Set (displacementSublevel (X := X) q A) := Subtype.val ⁻¹' L₀
  refine ⟨L, (displacementSublevel_closed hG.2.1 q A).isClosedEmbedding_subtypeVal.isCompact_preimage hL₀, ?_⟩
  intro x
  obtain ⟨g, p, hp, hg⟩ := hcover x.val
  let v : ι → G := fun i => g⁻¹ * q i * g
  have hv : v ∈ Q := by
    refine ⟨?_, g, fun _ => rfl⟩
    intro i
    refine ⟨p, hp, ?_⟩
    have hd : dist p (v i • p) = dist (g • p) (q i • (g • p)) := by
      rw [← (hG.2.1 g).dist_eq]
      simp [v, mul_smul]
    rw [hd, hg]
    exact x.property i
  let r : G := rep ⟨v, hv⟩
  have hr (i : ι) : r⁻¹ * q i * r = g⁻¹ * q i * g := hrep ⟨v, hv⟩ i
  have hc : g * r⁻¹ ∈ tupleCentralizer q := by
    intro i
    change g * r⁻¹ * q i = q i * (g * r⁻¹)
    calc
      g * r⁻¹ * q i = g * (r⁻¹ * q i * r) * r⁻¹ := by group
      _ = g * (g⁻¹ * q i * g) * r⁻¹ := by rw [hr]
      _ = _ := by group
  let c : tupleCentralizer q := ⟨g * r⁻¹, hc⟩
  refine ⟨c, c⁻¹ • x, ?_, smul_inv_smul c x⟩
  change ((c⁻¹ • x).val) ∈ L₀
  apply Set.mem_iUnion.mpr
  refine ⟨⟨v, hv⟩, p, hp, ?_⟩
  change r • p = (g * r⁻¹)⁻¹ • x.val
  rw [← hg]
  simp only [mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]

/-- The finite-tuple geometric centralizer theorem, with no commutation
hypothesis on the tuple itself and no dimension hypothesis. -/
theorem geometric_tupleCentralizer [Finite ι] [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (q : ι → G) (A : ℝ) (hA : 0 ≤ A) :
    letI := sublevelAction hG.2.1 q A
    GeometricAction (tupleCentralizer q) (displacementSublevel (X := X) q A) := by
  let := sublevelAction hG.2.1 q A
  exact ⟨CAT0_subtype hG.1 (displacementSublevel_convex hG.1 hG.2.1 q A),
    sublevelAction_isometry hG.2.1 q A, sublevelAction_proper hG.2.1 hG.2.2.1 q A,
    sublevelAction_cocompact hG q A hA⟩

lemma sublevelAction_stableLength (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) (x : displacementSublevel (X := X) q A)
    (g : tupleCentralizer q) :
    letI := sublevelAction hi q A
    stableLengthAt x g = stableLengthAt x.val g.val := by
  rfl

lemma exists_sublevel_nonempty [Finite ι] [Nonempty X] (q : ι → G) :
    ∃ A : ℝ, 0 ≤ A ∧ Nonempty (displacementSublevel (X := X) q A) := by
  classical
  let := Fintype.ofFinite ι
  let x : X := Classical.choice inferInstance
  refine ⟨∑ i : ι, dist x (q i • x), Finset.sum_nonneg (fun _ _ => dist_nonneg), ?_⟩
  refine ⟨⟨x, fun i => ?_⟩⟩
  exact Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (dist_nonneg : 0 ≤ dist x (q j • x))) (Finset.mem_univ i)

lemma sublevel_properSpace [ProperSpace X]
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (q : ι → G) (A : ℝ) :
    ProperSpace (displacementSublevel (X := X) q A) :=
  ProperSpace.of_isClosed (displacementSublevel_closed hi q A)

end CommonCentralizerGeometry
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0.TriangleMesh

variable {F V : Type*}

noncomputable def foldPartner (f g : F) (d : F × Fin 3) : F × Fin 3 := by
  classical
  exact if d.1 = f then (g,-d.2) else if d.1 = g then (f,-d.2) else d

structure Fold (M : TriangleMesh F V) where
  f : F
  g : F
  ne : f ≠ g
  seam : M.mate (f,0) = (g,0)
  internal : ∀ d, (d.1 = f ∨ d.1 = g) →
    ((M.mate d).1 = f ∨ (M.mate d).1 = g) → M.mate d = foldPartner f g d

namespace Fold
variable {M : TriangleMesh F V} (C : M.Fold)

def Removed (d : F × Fin 3) : Prop := d.1 = C.f ∨ d.1 = C.g
abbrev Kept := {f : F // f ≠ C.f ∧ f ≠ C.g}
noncomputable abbrev partner := foldPartner C.f C.g

@[simp] lemma partner_f (i : Fin 3) : C.partner (C.f,i) = (C.g,-i) := by
  simp [partner, foldPartner]
@[simp] lemma partner_g (i : Fin 3) : C.partner (C.g,i) = (C.f,-i) := by
  simp [partner, foldPartner, C.ne.symm]

lemma partner_outside (d : F × Fin 3) (hd : ¬ C.Removed d) : C.partner d = d := by
  simp only [Removed, not_or] at hd
  simp [partner, foldPartner, hd.1, hd.2]

@[simp] lemma partner_partner (d : F × Fin 3) : C.partner (C.partner d) = d := by
  by_cases hf : d.1 = C.f
  · rcases d with ⟨f,i⟩
    dsimp only at hf
    subst f
    simp
  · by_cases hg : d.1 = C.g
    · rcases d with ⟨g,i⟩
      dsimp only at hg
      subst g
      simp
    · rw [C.partner_outside d (by simpa [Removed] using And.intro hf hg)]
      exact C.partner_outside d (by simpa [Removed] using And.intro hf hg)

lemma partner_removed (d : F × Fin 3) (hd : C.Removed d) : C.Removed (C.partner d) := by
  rcases d with ⟨f,i⟩
  rcases hd with hf | hf <;> dsimp only at hf <;> subst f
  · simp [Removed]
  · simp [Removed]

lemma partner_ne (d : F × Fin 3) (hd : C.Removed d) : C.partner d ≠ d := by
  rcases d with ⟨f,i⟩
  rcases hd with hf | hf <;> dsimp only at hf <;> subst f
  · intro h
    exact C.ne.symm (congrArg Prod.fst (C.partner_f i ▸ h))
  · intro h
    exact C.ne (congrArg Prod.fst (C.partner_g i ▸ h))

@[simp] lemma mate_seam_reverse : M.mate (C.g,0) = (C.f,0) := by
  rw [← C.seam, M.mate_mate]

lemma mate_partner_outside (d : F × Fin 3) (hd : C.Removed d)
    (hm : ¬ C.Removed (M.mate d)) : ¬ C.Removed (M.mate (C.partner d)) := by
  intro h
  have he := C.internal (C.partner d) (C.partner_removed d hd) h
  change M.mate (C.partner d) = C.partner (C.partner d) at he
  rw [C.partner_partner] at he
  have he' := congrArg M.mate he
  rw [M.mate_mate] at he'
  exact hm (he' ▸ C.partner_removed d hd)

noncomputable def splice (d : F × Fin 3) : F × Fin 3 := by
  classical
  exact if C.Removed (M.mate d) then M.mate (C.partner (M.mate d)) else M.mate d

lemma splice_inside (d : F × Fin 3) (h : C.Removed (M.mate d)) :
    C.splice d = M.mate (C.partner (M.mate d)) := by simp [splice, h]
lemma splice_outside (d : F × Fin 3) (h : ¬ C.Removed (M.mate d)) :
    C.splice d = M.mate d := by simp [splice, h]

lemma splice_kept (d : F × Fin 3) (hd : ¬ C.Removed d) : ¬ C.Removed (C.splice d) := by
  by_cases hm : C.Removed (M.mate d)
  · rw [C.splice_inside d hm]
    exact C.mate_partner_outside (M.mate d) hm (by simpa using hd)
  · rw [C.splice_outside d hm]
    exact hm

lemma splice_splice (d : F × Fin 3) (hd : ¬ C.Removed d) : C.splice (C.splice d) = d := by
  by_cases hm : C.Removed (M.mate d)
  · rw [C.splice_inside d hm]
    rw [C.splice_inside _ (by simpa using C.partner_removed (M.mate d) hm)]
    simp
  · rw [C.splice_outside d hm]
    rw [C.splice_outside _ (by simpa using hd)]
    simp

lemma splice_ne (d : F × Fin 3) (_hd : ¬ C.Removed d) : C.splice d ≠ d := by
  by_cases hm : C.Removed (M.mate d)
  · rw [C.splice_inside d hm]
    intro he
    have he' := congrArg M.mate he
    rw [M.mate_mate] at he'
    exact C.partner_ne (M.mate d) hm he'
  · rw [C.splice_outside d hm]
    exact M.mate_ne d

noncomputable def merge (v : V) : V := by
  classical
  exact if v = M.tail (C.g,2) then M.tail (C.f,2) else v

lemma merge_opposite : C.merge (M.tail (C.g,2)) = C.merge (M.tail (C.f,2)) := by
  simp only [merge, ite_true]
  split_ifs <;> rfl

lemma tail_seam : M.tail (C.g,0) = M.tail (C.f,1) := by
  have hh := M.tail_mate (C.f,0)
  simpa [C.seam] using hh

lemma tail_seam_reverse : M.tail (C.g,1) = M.tail (C.f,0) := by
  have hh := M.tail_mate (C.g,0)
  simpa using hh.symm

lemma merge_tail_partner (d : F × Fin 3) (hd : C.Removed d) :
    C.merge (M.tail (rotate (C.partner d))) = C.merge (M.tail d) := by
  rcases d with ⟨f,i⟩
  rcases hd with hf | hf <;> dsimp only at hf <;> subst f
  · fin_cases i
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam_reverse
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using C.merge_opposite
  · fin_cases i
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam.symm
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam_reverse.symm
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using C.merge_opposite.symm

abbrev oldDart (d : C.Kept × Fin 3) : F × Fin 3 := (d.1.val,d.2)

lemma oldDart_kept (d : C.Kept × Fin 3) : ¬ C.Removed (C.oldDart d) :=
  not_or.mpr d.1.property

noncomputable def newMate (d : C.Kept × Fin 3) : C.Kept × Fin 3 :=
  (⟨(C.splice (C.oldDart d)).1, not_or.mp (C.splice_kept _ (C.oldDart_kept d))⟩,
    (C.splice (C.oldDart d)).2)

@[simp] lemma oldDart_newMate (d : C.Kept × Fin 3) :
    C.oldDart (C.newMate d) = C.splice (C.oldDart d) := rfl

lemma oldDart_injective : Function.Injective C.oldDart := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have ha : a = b := Subtype.ext (congrArg Prod.fst h)
  have hi : i = j := congrArg Prod.snd h
  simp_all

lemma newMate_involutive : Function.Involutive C.newMate := by
  intro d
  apply C.oldDart_injective
  rw [C.oldDart_newMate, C.oldDart_newMate, C.splice_splice _ (C.oldDart_kept d)]

noncomputable def mesh : TriangleMesh C.Kept V where
  mate := C.newMate_involutive.toPerm
  mate_involutive := C.newMate_involutive
  mate_ne d h := C.splice_ne _ (C.oldDart_kept d) (congrArg C.oldDart h)
  tail d := C.merge (M.tail (C.oldDart d))
  tail_mate d := by
    change C.merge (M.tail (C.splice (C.oldDart d))) = C.merge (M.tail (rotate (C.oldDart d)))
    by_cases hm : C.Removed (M.mate (C.oldDart d))
    · rw [C.splice_inside _ hm, M.tail_mate]
      rw [show (M.tail ((C.partner (M.mate (C.oldDart d))).1,
        (C.partner (M.mate (C.oldDart d))).2+1)) = M.tail (rotate (C.partner (M.mate (C.oldDart d)))) from rfl]
      rw [C.merge_tail_partner _ hm, M.tail_mate]
      rfl
    · rw [C.splice_outside _ hm, M.tail_mate]
      rfl

def toNewDart (d : F × Fin 3) (hd : ¬ C.Removed d) : C.Kept × Fin 3 :=
  (⟨d.1, not_or.mp hd⟩,d.2)

@[simp] lemma oldDart_toNewDart (d : F × Fin 3) (hd : ¬ C.Removed d) :
    C.oldDart (C.toNewDart d hd) = d := rfl

@[simp] lemma toNewDart_oldDart (d : C.Kept × Fin 3) :
    C.toNewDart (C.oldDart d) (C.oldDart_kept d) = d := rfl

noncomputable def sideValue (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3) : ℝ := by
  classical
  exact if h : C.Removed (M.mate d) then 0 else -w (C.toNewDart (M.mate d) h)

lemma sideValue_partner (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) (d : F × Fin 3) (hd : C.Removed d) :
    C.sideValue w (C.partner d) = -C.sideValue w d := by
  by_cases hm : C.Removed (M.mate d)
  · have he : M.mate d = C.partner d := C.internal d hd hm
    have he' : M.mate (C.partner d) = d := by rw [← he, M.mate_mate]
    simp [sideValue, hm, he', hd]
  · have hm' := C.mate_partner_outside d hd hm
    have hs := ha (C.toNewDart (M.mate d) hm)
    have he : C.newMate (C.toNewDart (M.mate d) hm) =
        C.toNewDart (M.mate (C.partner d)) hm' := by
      apply C.oldDart_injective
      rw [C.oldDart_newMate, C.oldDart_toNewDart, C.oldDart_toNewDart]
      rw [C.splice_inside _ (by simpa using hd), M.mate_mate]
    rw [he] at hs
    simp only [sideValue, dite_eq_right hm, dite_eq_right hm', hs, neg_neg]

noncomputable def extension (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3) : ℝ := by
  classical
  exact if d = (C.f,0) then -(C.sideValue w (C.f,1) + C.sideValue w (C.f,2))
    else if d = (C.g,0) then C.sideValue w (C.f,1) + C.sideValue w (C.f,2)
    else if h : C.Removed d then C.sideValue w d else w (C.toNewDart d h)

lemma extension_outside (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3) (hd : ¬ C.Removed d) :
    C.extension w d = w (C.toNewDart d hd) := by
  have hf : d ≠ (C.f,0) := fun h => hd (Or.inl (congrArg Prod.fst h))
  have hg : d ≠ (C.g,0) := fun h => hd (Or.inr (congrArg Prod.fst h))
  simp [extension, hf, hg, hd]

@[simp] lemma extension_f_zero (w : C.Kept × Fin 3 → ℝ) :
    C.extension w (C.f,0) = -(C.sideValue w (C.f,1) + C.sideValue w (C.f,2)) := by
  simp [extension]

@[simp] lemma extension_g_zero (w : C.Kept × Fin 3 → ℝ) :
    C.extension w (C.g,0) = C.sideValue w (C.f,1) + C.sideValue w (C.f,2) := by
  simp [extension, C.ne.symm]

lemma extension_removed_nonzero (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3)
    (hd : C.Removed d) (hf : d ≠ (C.f,0)) (hg : d ≠ (C.g,0)) :
    C.extension w d = C.sideValue w d := by simp [extension, hf, hg, hd]

lemma extension_mate (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) (d : F × Fin 3) :
    C.extension w (M.mate d) = -C.extension w d := by
  by_cases hf : d = (C.f,0)
  · subst d
    rw [C.seam, C.extension_g_zero, C.extension_f_zero, neg_neg]
  by_cases hg : d = (C.g,0)
  · subst d
    rw [C.mate_seam_reverse, C.extension_f_zero, C.extension_g_zero]
  have hmf : M.mate d ≠ (C.f,0) := by
    intro he
    apply hg
    calc
      d = M.mate (M.mate d) := (M.mate_mate d).symm
      _ = (C.g,0) := by rw [he, C.seam]
  have hmg : M.mate d ≠ (C.g,0) := by
    intro he
    apply hf
    calc
      d = M.mate (M.mate d) := (M.mate_mate d).symm
      _ = (C.f,0) := by rw [he, C.mate_seam_reverse]
  by_cases hd : C.Removed d
  · rw [C.extension_removed_nonzero w d hd hf hg]
    by_cases hm : C.Removed (M.mate d)
    · rw [C.extension_removed_nonzero w _ hm hmf hmg]
      have he : M.mate d = C.partner d := C.internal d hd hm
      rw [he, C.sideValue_partner w ha d hd]
    · rw [C.extension_outside w _ hm]
      simp [sideValue, hm]
  · rw [C.extension_outside w d hd]
    by_cases hm : C.Removed (M.mate d)
    · rw [C.extension_removed_nonzero w _ hm hmf hmg]
      simp [sideValue, hd]
    · rw [C.extension_outside w _ hm]
      have he : C.newMate (C.toNewDart d hd) = C.toNewDart (M.mate d) hm := by
        apply C.oldDart_injective
        rw [C.oldDart_newMate, C.oldDart_toNewDart, C.oldDart_toNewDart, C.splice_outside d hm]
      simpa only [he] using ha (C.toNewDart d hd)

lemma sideValue_g_one (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) :
    C.sideValue w (C.g,1) = -C.sideValue w (C.f,2) := by
  simpa [Fin.neg_def] using C.sideValue_partner w ha (C.f,2) (Or.inl rfl)

lemma sideValue_g_two (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) :
    C.sideValue w (C.g,2) = -C.sideValue w (C.f,1) := by
  simpa [Fin.neg_def] using C.sideValue_partner w ha (C.f,1) (Or.inl rfl)

lemma extension_face (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d)
    (hc : ∀ f, ∑ i : Fin 3, w (f,i) = 0) (f : F) :
    ∑ i : Fin 3, C.extension w (f,i) = 0 := by
  classical
  by_cases hf : f = C.f
  · subst f
    simp only [Fin.sum_univ_three, C.extension_f_zero]
    rw [C.extension_removed_nonzero w (C.f,1) (Or.inl rfl) (by simp) (by simp),
      C.extension_removed_nonzero w (C.f,2) (Or.inl rfl) (by simp) (by simp)]
    ring
  by_cases hg : f = C.g
  · subst f
    simp only [Fin.sum_univ_three, C.extension_g_zero]
    rw [C.extension_removed_nonzero w (C.g,1) (Or.inr rfl) (by simp) (by simp),
      C.extension_removed_nonzero w (C.g,2) (Or.inr rfl) (by simp) (by simp),
      C.sideValue_g_one w ha, C.sideValue_g_two w ha]
    ring
  · have hd (i : Fin 3) : ¬ C.Removed (f,i) := not_or.mpr ⟨hf,hg⟩
    simpa only [C.extension_outside w _ (hd _), toNewDart] using hc ⟨f,hf,hg⟩

/-- Deleting the opposite pair preserves exactness of edge cocycles. -/
theorem mesh_exact (he : M.Exact) : C.mesh.Exact := by
  intro w ha hc
  change ∀ d, w (C.newMate d) = -w d at ha
  obtain ⟨p,hp⟩ := he (C.extension w) (C.extension_mate w ha) (C.extension_face w ha hc)
  have hfg : p (M.tail (C.f,2)) = p (M.tail (C.g,2)) := by
    have hf := hp (C.f,1)
    have hg := hp (C.g,2)
    rw [C.extension_removed_nonzero w (C.f,1) (Or.inl rfl) (by simp) (by simp)] at hf
    rw [C.extension_removed_nonzero w (C.g,2) (Or.inr rfl) (by simp) (by simp),
      C.sideValue_g_two w ha] at hg
    change C.sideValue w (C.f,1) = p (M.tail (C.f,2)) - p (M.tail (C.f,1)) at hf
    change -C.sideValue w (C.f,1) = p (M.tail (C.g,0)) - p (M.tail (C.g,2)) at hg
    rw [C.tail_seam] at hg
    linarith
  have hm (v : V) : p (C.merge v) = p v := by
    unfold merge
    split_ifs with h
    · rw [h, hfg]
    · rfl
  refine ⟨p, fun d => ?_⟩
  have hd := hp (C.oldDart d)
  rw [C.extension_outside w _ (C.oldDart_kept d), C.toNewDart_oldDart] at hd
  change w d = p (C.merge (M.tail (rotate (C.oldDart d)))) - p (C.merge (M.tail (C.oldDart d)))
  rw [hm, hm]
  exact hd

end Fold
end ArtinCAT0.TriangleMesh
namespace ArtinCAT0.TriangleMesh
variable {F V : Type*} (M : TriangleMesh F V)

noncomputable def active : TriangleMesh F (Set.range M.tail) where
  mate := M.mate
  mate_involutive := M.mate_involutive
  mate_ne := M.mate_ne
  tail d := ⟨M.tail d, Set.mem_range_self d⟩
  tail_mate d := Subtype.ext (M.tail_mate d)

lemma active_exact (he : M.Exact) : M.active.Exact := by
  intro w ha hc
  rcases he w ha hc with ⟨p,hp⟩
  exact ⟨fun v => p v.val, hp⟩

lemma active_surjective : Function.Surjective M.active.tail := by
  rintro ⟨v,d,rfl⟩
  exact ⟨d,rfl⟩

def phaseEquiv (c : F → Fin 3) : Equiv.Perm (F × Fin 3) where
  toFun d := (d.1,d.2+c d.1)
  invFun d := (d.1,d.2-c d.1)
  left_inv d := by ext <;> simp
  right_inv d := by ext <;> simp

@[simp] lemma phaseEquiv_apply (c : F → Fin 3) (d : F × Fin 3) :
    phaseEquiv c d = (d.1,d.2+c d.1) := rfl
@[simp] lemma phaseEquiv_symm_apply (c : F → Fin 3) (d : F × Fin 3) :
    (phaseEquiv c).symm d = (d.1,d.2-c d.1) := rfl

lemma phaseEquiv_rotate (c : F → Fin 3) (d : F × Fin 3) :
    phaseEquiv c (rotate d) = rotate (phaseEquiv c d) := by
  ext <;> simp [add_comm, add_left_comm, add_assoc]

noncomputable def rephase (c : F → Fin 3) : TriangleMesh F V where
  mate := (phaseEquiv c).symm * M.mate * phaseEquiv c
  mate_involutive d := by
    change (phaseEquiv c).symm (M.mate (phaseEquiv c ((phaseEquiv c).symm (M.mate (phaseEquiv c d))))) = d
    simp
  mate_ne d h := by
    apply M.mate_ne (phaseEquiv c d)
    have he := congrArg (phaseEquiv c) h
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using he
  tail d := M.tail (phaseEquiv c d)
  tail_mate d := by
    change M.tail (phaseEquiv c ((phaseEquiv c).symm (M.mate (phaseEquiv c d)))) =
      M.tail (phaseEquiv c (rotate d))
    rw [Equiv.apply_symm_apply, M.tail_mate, phaseEquiv_rotate]
    rfl

lemma rephase_exact (c : F → Fin 3) (he : M.Exact) : (M.rephase c).Exact := by
  intro w ha hc
  let w' : F × Fin 3 → ℝ := fun d => w ((phaseEquiv c).symm d)
  have ha' : ∀ d, w' (M.mate d) = -w' d := by
    intro d
    simpa only [w', rephase, Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
      ha ((phaseEquiv c).symm d)
  have hc' : ∀ f, ∑ i : Fin 3, w' (f,i) = 0 := by
    intro f
    let e : Equiv.Perm (Fin 3) :=
      { toFun := fun i => i-c f
        invFun := fun i => i+c f
        left_inv := by intro i; simp
        right_inv := by intro i; simp }
    change ∑ i : Fin 3, w (f,e i) = 0
    rw [show (∑ i : Fin 3, w (f,e i)) = ∑ i : Fin 3, w (f,i) from
      Equiv.sum_comp e (fun i => w (f,i))]
    exact hc f
  rcases he w' ha' hc' with ⟨p,hp⟩
  refine ⟨p, fun d => ?_⟩
  have hh := hp (phaseEquiv c d)
  simpa only [w', Equiv.symm_apply_apply, rephase, phaseEquiv_rotate] using hh

end ArtinCAT0.TriangleMesh
namespace ArtinCAT0

def xLetter (b i : Fin 3) : Fin 9 :=
  if i = 0 then ⟨b.val, by omega⟩ else if i = 1 then ⟨(b+1).val, by omega⟩
  else ⟨3+b.val, by omega⟩

def hLetter (b : Fin 3) : Fin 9 := ⟨6+b.val, by omega⟩

def positiveDirection (q : Fin 9) : LinkDirection := ⟨q.val, by omega⟩
def negativeDirection (q : Fin 9) : LinkDirection := ⟨q.val+9, by omega⟩
def reverseDirection (d : LinkDirection) : LinkDirection := d+9

@[simp] lemma reverseDirection_reverseDirection (d : LinkDirection) :
    reverseDirection (reverseDirection d) = d := by
  unfold reverseDirection
  apply Fin.ext
  omega

/-- Directed sides, retaining the literal nine labels, not just their group values. -/
def cellDirection (b i s t : Fin 3) : LinkDirection :=
  if s = 0 ∧ t = 1 then positiveDirection (xLetter b i)
  else if s = 1 ∧ t = 2 then positiveDirection (xLetter b (i+1))
  else if s = 0 ∧ t = 2 then positiveDirection (hLetter b)
  else if s = 1 ∧ t = 0 then negativeDirection (xLetter b i)
  else if s = 2 ∧ t = 1 then negativeDirection (xLetter b (i+1))
  else negativeDirection (hLetter b)

lemma cellDirection_reverse : ∀ b i s t : Fin 3, s ≠ t →
    cellDirection b i t s = reverseDirection (cellDirection b i s t) := by decide

abbrev CornerOrder := Equiv.Perm (Fin 3)

def cellFlag (b i : Fin 3) (p : CornerOrder) : LinkDirection × LinkDirection :=
  (cellDirection b i (p 0) (p 1), cellDirection b i (p 0) (p 2))

lemma cellFlag_injective : Function.Injective
    (fun z : Fin 3 × Fin 3 × CornerOrder => cellFlag z.1 z.2.1 z.2.2) := by decide

lemma cellFlag_adjacent : ∀ b i : Fin 3, ∀ p : CornerOrder,
    (cellFlag b i p).2 ∈ linkNeighbors (cellFlag b i p).1 := by decide

lemma cellDirection_injective : ∀ b i : Fin 3, ∀ s t s' t' : Fin 3,
    s ≠ t → s' ≠ t' → cellDirection b i s t = cellDirection b i s' t' →
    s = s' ∧ t = t' := by decide

/-- Orientation sign of the vertex correspondence. -/
def cornerSign (p : CornerOrder) : ℤ := if p 1 = p 0 + 1 then 1 else -1

def reverseCorner (p : CornerOrder) : CornerOrder := p * Equiv.swap 1 2

lemma cornerSign_reverse : ∀ p : CornerOrder,
    cornerSign (reverseCorner p) = -cornerSign p := by decide

structure TargetTriangle where
  base : TriangleGroup
  block : Fin 3
  rel : Fin 3

def TargetTriangle.vertex (c : TargetTriangle) (i : Fin 3) : TriangleGroup :=
  c.base * (if i = 0 then 1 else if i = 1 then triangleX c.block c.rel else triangleH c.block)

def TargetTriangle.direction (c : TargetTriangle) (i j : Fin 3) :=
  cellDirection c.block c.rel i j

lemma TargetTriangle.vertex_injective (c : TargetTriangle) : Function.Injective c.vertex := by
  intro i j he
  have h := congrArg (fun g => Multiplicative.toAdd (triangleExponent g)) he
  have hi : Multiplicative.toAdd (triangleExponent (c.vertex i)) =
      Multiplicative.toAdd (triangleExponent c.base) + (i.val : ℤ) := by
    fin_cases i <;> simp [TargetTriangle.vertex]
  have hj : Multiplicative.toAdd (triangleExponent (c.vertex j)) =
      Multiplicative.toAdd (triangleExponent c.base) + (j.val : ℤ) := by
    fin_cases j <;> simp [TargetTriangle.vertex]
  rw [hi,hj] at h
  apply Fin.ext
  omega

namespace TriangleMesh
variable {F V : Type*} (M : TriangleMesh F V)

/-- Complete cell identities and vertex correspondences; compatibility includes
labelled directions rather than merely equal group elements. -/
structure Labeling where
  cell : F → TargetTriangle
  order : F → CornerOrder
  vertex : V → TriangleGroup
  vertex_tail : ∀ d, vertex (M.tail d) = (cell d.1).vertex (order d.1 d.2)
  mate_compatibility : ∀ d,
    (cell (M.mate d).1).direction (order (M.mate d).1 (M.mate d).2)
      (order (M.mate d).1 ((M.mate d).2+1)) =
    reverseDirection ((cell d.1).direction (order d.1 d.2) (order d.1 (d.2+1)))

namespace Labeling
variable {M} (L : M.Labeling)

def direction (d : F × Fin 3) : LinkDirection :=
  (L.cell d.1).direction (L.order d.1 d.2) (L.order d.1 (d.2+1))

@[simp] lemma direction_mate (d : F × Fin 3) :
    L.direction (M.mate d) = reverseDirection (L.direction d) := L.mate_compatibility d

def cornerShift (i : Fin 3) : CornerOrder where
  toFun j := i+j
  invFun j := j-i
  left_inv j := by simp
  right_inv j := by simp

@[simp] lemma cornerShift_apply (i j : Fin 3) : cornerShift i j = i+j := rfl

def cornerAt (d : F × Fin 3) : CornerOrder := L.order d.1 * cornerShift d.2

lemma direction_turn (d : F × Fin 3) :
    L.direction (M.turn d) = (L.cell d.1).direction (L.order d.1 d.2) (L.order d.1 (d.2+2)) := by
  rw [turn_apply, L.direction_mate]
  change reverseDirection (cellDirection _ _ (L.order d.1 (d.2-1))
    (L.order d.1 (d.2-1+1))) = _
  rw [sub_add_cancel, ← cellDirection_reverse]
  · congr 2
    apply Fin.ext
    omega
  · apply (L.order d.1).injective.ne
    intro h
    have := congrArg Fin.val h
    omega

lemma flag_cornerAt (d : F × Fin 3) :
    cellFlag (L.cell d.1).block (L.cell d.1).rel (L.cornerAt d) =
      (L.direction d, L.direction (M.turn d)) := by
  rw [L.direction_turn]
  simp [cellFlag, cornerAt, direction, TargetTriangle.direction]

lemma link_adjacent (d : F × Fin 3) :
    L.direction (M.turn d) ∈ linkNeighbors (L.direction d) := by
  have h := cellFlag_adjacent (L.cell d.1).block (L.cell d.1).rel (L.cornerAt d)
  simpa only [L.flag_cornerAt] using h

include L in
lemma mate_face_ne (d : F × Fin 3) : (M.mate d).1 ≠ d.1 := by
  intro he
  have h := L.direction_mate d
  simp only [direction, he, TargetTriangle.direction] at h
  have hf : ∀ (b i : Fin 3) (p : CornerOrder) (j k : Fin 3),
      cellDirection b i (p j) (p (j+1)) ≠
        reverseDirection (cellDirection b i (p k) (p (k+1))) := by decide
  exact hf _ _ _ _ _ h

lemma cellFlag_reverse (b i : Fin 3) (p : CornerOrder) :
    cellFlag b i (reverseCorner p) = (cellFlag b i p).swap := by
  simp [cellFlag, reverseCorner, show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]

lemma backtrack_cell (d : F × Fin 3)
    (hb : L.direction (M.turn (M.turn d)) = L.direction d) :
    L.cell (M.turn d).1 = L.cell d.1 ∧
    L.cornerAt (M.turn d) = reverseCorner (L.cornerAt d) := by
  have hf : cellFlag (L.cell (M.turn d).1).block (L.cell (M.turn d).1).rel
      (L.cornerAt (M.turn d)) =
      cellFlag (L.cell d.1).block (L.cell d.1).rel (reverseCorner (L.cornerAt d)) := by
    rw [L.flag_cornerAt, cellFlag_reverse, L.flag_cornerAt, hb]
    rfl
  have hh := cellFlag_injective
    (a₁ := ((L.cell (M.turn d).1).block, (L.cell (M.turn d).1).rel, L.cornerAt (M.turn d)))
    (a₂ := ((L.cell d.1).block, (L.cell d.1).rel, reverseCorner (L.cornerAt d))) hf
  have hblock := congrArg Prod.fst hh
  have hrel := congrArg (fun x => x.2.1) hh
  have hp := congrArg (fun x => x.2.2) hh
  dsimp only at hblock hrel hp
  refine ⟨?_,hp⟩
  have hv : (L.cell (M.turn d).1).vertex (L.order (M.turn d).1 (M.turn d).2) =
      (L.cell d.1).vertex (L.order d.1 d.2) := by
    rw [← L.vertex_tail, ← L.vertex_tail, M.tail_turn]
  have hp0 := Equiv.congr_fun hp 0
  simp only [cornerAt, Equiv.Perm.mul_apply, cornerShift_apply, add_zero,
    reverseCorner, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2)] at hp0
  rw [hp0] at hv
  simp only [TargetTriangle.vertex, hblock, hrel, mul_left_inj] at hv
  cases hc : L.cell (M.turn d).1
  cases hd : L.cell d.1
  simp_all

noncomputable def active : M.active.Labeling where
  cell := L.cell
  order := L.order
  vertex v := L.vertex v.val
  vertex_tail := L.vertex_tail
  mate_compatibility := L.mate_compatibility

noncomputable def rephase (c : F → Fin 3) : (M.rephase c).Labeling where
  cell := L.cell
  order f := L.order f * cornerShift (c f)
  vertex := L.vertex
  vertex_tail d := by
    simpa [TriangleMesh.rephase, phaseEquiv, cornerShift, add_comm] using
      L.vertex_tail (d.1,d.2+c d.1)
  mate_compatibility d := by
    have hh := L.mate_compatibility (phaseEquiv c d)
    change cellDirection _ _ _ _ = reverseDirection (cellDirection _ _ _ _) at hh ⊢
    simp only [TriangleMesh.rephase, Equiv.Perm.mul_apply, phaseEquiv_apply,
      phaseEquiv_symm_apply, cornerShift_apply] at *
    simpa [add_comm, add_left_comm, add_assoc] using hh

lemma orders_of_seam {f g : F} (he : L.cell g = L.cell f)
    (hs : M.mate (f,0) = (g,0)) :
    L.order g 0 = L.order f 1 ∧ L.order g 1 = L.order f 0 := by
  have ht0 : M.tail (g,0) = M.tail (f,1) := by
    simpa [hs] using M.tail_mate (f,0)
  have ht1 : M.tail (g,1) = M.tail (f,0) := by
    simpa [hs, rotate_apply] using M.tail_rotate_mate (f,0)
  constructor
  · apply (L.cell f).vertex_injective
    rw [← he, ← L.vertex_tail (g,0), ht0, L.vertex_tail (f,1), he]
  · apply (L.cell f).vertex_injective
    rw [← he, ← L.vertex_tail (g,1), ht1, L.vertex_tail (f,0), he]

lemma order_seam_remaining : ∀ p q : CornerOrder,
    q 0 = p 1 → q 1 = p 0 → q 2 = p 2 := by decide

lemma order_seam_sign : ∀ p q : CornerOrder,
    q 0 = p 1 → q 1 = p 0 → cornerSign q = -cornerSign p := by decide

lemma order_seam_mate : ∀ (b k : Fin 3) (p q : CornerOrder),
    q 0 = p 1 → q 1 = p 0 → ∀ i j : Fin 3,
    cellDirection b k (q j) (q (j+1)) =
      reverseDirection (cellDirection b k (p i) (p (i+1))) → j = -i := by decide

noncomputable def seamFold {f g : F} (he : L.cell g = L.cell f)
    (hs : M.mate (f,0) = (g,0)) : M.Fold where
  f := f
  g := g
  ne := by
    intro h
    have hh := L.mate_face_ne (f,0)
    exact hh (by simpa [hs] using h.symm)
  seam := hs
  internal d hd hm := by
    obtain ⟨h0,h1⟩ := L.orders_of_seam he hs
    rcases d with ⟨a,i⟩
    rcases hm with hm | hm
    · rcases hd with hd | hd
      · dsimp only at *
        exact False.elim (L.mate_face_ne (a,i) (hm.trans hd.symm))
      · dsimp only at hd hm
        subst a
        have hh := L.mate_compatibility (g,i)
        simp only [hm, he, TargetTriangle.direction] at hh
        have hj := order_seam_mate _ _ (L.order g) (L.order f) h1.symm h0.symm i _ hh
        apply Prod.ext
        · simpa [foldPartner, show g ≠ f from fun h => L.mate_face_ne (f,0) (by simp [hs,h])]
        · simpa [foldPartner, show g ≠ f from fun h => L.mate_face_ne (f,0) (by simp [hs,h])] using hj
    · rcases hd with hd | hd
      · dsimp only at hd hm
        subst a
        have hh := L.mate_compatibility (f,i)
        simp only [hm, he, TargetTriangle.direction] at hh
        have hj := order_seam_mate _ _ (L.order f) (L.order g) h0 h1 i _ hh
        apply Prod.ext
        · simpa [foldPartner] using hm
        · simpa [foldPartner] using hj
      · dsimp only at *
        exact False.elim (L.mate_face_ne (a,i) (hm.trans hd.symm))

lemma vertex_merge (C : M.Fold) (he : L.cell C.g = L.cell C.f) (v : V) :
    L.vertex (C.merge v) = L.vertex v := by
  have hh := L.orders_of_seam he C.seam
  have hp := order_seam_remaining (L.order C.f) (L.order C.g) hh.1 hh.2
  unfold Fold.merge
  split_ifs with hv
  · subst v
    rw [L.vertex_tail, L.vertex_tail, he, hp]
  · rfl

lemma direction_partner (C : M.Fold) (he : L.cell C.g = L.cell C.f)
    (d : F × Fin 3) (hd : C.Removed d) :
    L.direction (C.partner d) = reverseDirection (L.direction d) := by
  have hh := L.orders_of_seam he C.seam
  have hc : ∀ (b k : Fin 3) (p q : CornerOrder),
      q 0 = p 1 → q 1 = p 0 → ∀ i : Fin 3,
      cellDirection b k (q (-i)) (q (-i+1)) =
        reverseDirection (cellDirection b k (p i) (p (i+1))) := by decide
  rcases d with ⟨f,i⟩
  rcases hd with hd | hd <;> dsimp only at hd <;> subst f
  · simpa only [C.partner_f, direction, he, TargetTriangle.direction] using
      hc (L.cell C.f).block (L.cell C.f).rel (L.order C.f) (L.order C.g) hh.1 hh.2 i
  · simpa only [C.partner_g, direction, he, TargetTriangle.direction] using
      hc (L.cell C.f).block (L.cell C.f).rel (L.order C.g) (L.order C.f) hh.2.symm hh.1.symm i

noncomputable def folded (C : M.Fold) (he : L.cell C.g = L.cell C.f) : C.mesh.Labeling where
  cell f := L.cell f.val
  order f := L.order f.val
  vertex := L.vertex
  vertex_tail d := by
    change L.vertex (C.merge (M.tail (C.oldDart d))) = _
    rw [L.vertex_merge C he, L.vertex_tail]
  mate_compatibility d := by
    change L.direction (C.splice (C.oldDart d)) = reverseDirection (L.direction (C.oldDart d))
    by_cases hm : C.Removed (M.mate (C.oldDart d))
    · rw [C.splice_inside _ hm, L.direction_mate, L.direction_partner C he _ hm,
        L.direction_mate, reverseDirection_reverseDirection]
    · rw [C.splice_outside _ hm, L.direction_mate]

lemma exists_equal_mates [Fintype F] [Nonempty F] (he : M.Exact) :
    ∃ d, L.cell (M.mate d).1 = L.cell d.1 := by
  classical
  let : Fintype (Set.range M.tail) := Fintype.ofFinite _
  obtain ⟨d,hd⟩ := M.active.exists_link_backtrack (M.active_exact he) M.active_surjective
    L.active.direction L.active.link_adjacent
  have hh := L.active.backtrack_cell d hd
  exact ⟨rotate.symm d, hh.1⟩

lemma exists_phased_seam [Fintype F] [Nonempty F] (he : M.Exact) :
    ∃ (c : F → Fin 3) (f g : F),
      (M.rephase c).mate (f,0) = (g,0) ∧ L.cell g = L.cell f := by
  classical
  obtain ⟨d,hd⟩ := L.exists_equal_mates he
  let f := d.1
  let g := (M.mate d).1
  have hne : g ≠ f := L.mate_face_ne d
  let c : F → Fin 3 := fun a => if a = f then d.2 else if a = g then (M.mate d).2 else 0
  refine ⟨c,f,g,?_,hd⟩
  change (phaseEquiv c).symm (M.mate (phaseEquiv c (f,0))) = (g,0)
  have hcf : c f = d.2 := by simp [c]
  have hcg : c g = (M.mate d).2 := by simp [c,hne]
  have hpf : phaseEquiv c (f,0) = d := by simp [f,hcf]
  rw [hpf]
  change ((M.mate d).1,(M.mate d).2 - c (M.mate d).1) = (g,0)
  rw [hcg]
  simp [g]

lemma cornerSign_shift : ∀ (p : CornerOrder) (i : Fin 3),
    cornerSign (p * cornerShift i) = cornerSign p := by decide

noncomputable def signedSum [Fintype F] (w : TargetTriangle → ℤ) : ℤ :=
  ∑ f, cornerSign (L.order f) * w (L.cell f)

@[simp] lemma signedSum_active [Fintype F] (w : TargetTriangle → ℤ) :
    L.active.signedSum w = L.signedSum w := rfl

@[simp] lemma signedSum_rephase [Fintype F] (c : F → Fin 3) (w : TargetTriangle → ℤ) :
    (L.rephase c).signedSum w = L.signedSum w := by
  simp only [signedSum, rephase, cornerSign_shift]

lemma signedSum_folded [Fintype F] (C : M.Fold) [Fintype C.Kept] (he : L.cell C.g = L.cell C.f)
    (w : TargetTriangle → ℤ) : (L.folded C he).signedSum w = L.signedSum w := by
  classical
  let q : F → ℤ := fun f => cornerSign (L.order f) * w (L.cell f)
  have hs := L.orders_of_seam he C.seam
  have hz : q C.g + q C.f = 0 := by
    dsimp only [q]
    rw [order_seam_sign (L.order C.f) (L.order C.g) hs.1 hs.2, he]
    ring
  have hf := Finset.sum_erase_add Finset.univ q (Finset.mem_univ C.f)
  have hg := Finset.sum_erase_add (Finset.univ.erase C.f) q
    (by simp [C.ne.symm] : C.g ∈ Finset.univ.erase C.f)
  have hh : (∑ x ∈ (Finset.univ.erase C.f).erase C.g, q x) = ∑ f : C.Kept, q f.val :=
    Finset.sum_subtype (Finset.univ.erase C.f |>.erase C.g)
    (p := fun f => f ≠ C.f ∧ f ≠ C.g) (F := inferInstance) (by intro f; simp [and_comm]) q
  change (∑ f : C.Kept, q f.val) = ∑ f, q f
  omega

end Labeling


/-- Every exact finite labelled triangular mesh has zero algebraic count on
 each individual target triangle. No manifold or embedding theorem is assumed. -/
theorem signed_counts_zero (w : TargetTriangle → ℤ) :
    ∀ (F : Type u) (V : Type v) [Fintype F] (M : TriangleMesh F V) (L : M.Labeling),
      M.Exact → L.signedSum w = 0 := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (F : Type u) (V : Type v) [Fintype F]
      (M : TriangleMesh F V) (L : M.Labeling),
      Fintype.card F = n → M.Exact → L.signedSum w = 0 by
    intro F V _ M L he
    exact hh (Fintype.card F) F V M L rfl he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F V _ M L hn he
    cases isEmpty_or_nonempty F with
    | inl hi =>
      let := hi
      simp [Labeling.signedSum]
    | inr hi =>
      let := hi
      obtain ⟨c,f,g,hs,hcell⟩ := L.exists_phased_seam he
      let C : (M.rephase c).Fold := (L.rephase c).seamFold hcell hs
      have hc : C.mesh.Exact := C.mesh_exact (M.rephase_exact c he)
      have hl : (L.rephase c).cell C.g = (L.rephase c).cell C.f := hcell
      have hcard : Fintype.card C.Kept < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := C.f) (by simp)
      have hp := ih (Fintype.card C.Kept) hcard C.Kept V C.mesh
        ((L.rephase c).folded C hl) rfl hc
      rw [(L.rephase c).signedSum_folded C hl, L.signedSum_rephase] at hp
      exact hp
end TriangleMesh
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

abbrev Mirror := Fin 3 × ℤ

def sideMirror (u : Fin 3) : Mirror :=
  if u = 0 then (0,0) else if u = 1 then (1,0) else (2,1)

def extraMirror (u : Fin 3) : Mirror :=
  if u = 0 then (2,0) else if u = 1 then (0,1) else (1,1)

/-- Action on x=k, y=k, x+y=k for the three side reflections of the
triangle x≥0, y≥0, x+y≤1 in equilateral coordinates. -/
def mirrorReflect (u : Fin 3) (d : Mirror) : Mirror :=
  if u = 0 then
    if d.1 = 0 then (0,-d.2) else if d.1 = 1 then (2,d.2) else (1,d.2)
  else if u = 1 then
    if d.1 = 0 then (2,d.2) else if d.1 = 1 then (1,-d.2) else (0,d.2)
  else
    if d.1 = 0 then (1,1-d.2) else if d.1 = 1 then (0,1-d.2) else (2,2-d.2)

lemma mirrorReflect_involutive (u : Fin 3) : Function.Involutive (mirrorReflect u) := by
  rintro ⟨k,n⟩
  fin_cases u <;> fin_cases k <;> simp [mirrorReflect]

lemma mirrorReflect_braid (u : Fin 3) (d : Mirror) :
    mirrorReflect u (mirrorReflect (u+1) (mirrorReflect u d)) =
      mirrorReflect (u+1) (mirrorReflect u (mirrorReflect (u+1) d)) := by
  rcases d with ⟨k,n⟩
  fin_cases u <;> fin_cases k <;> simp [mirrorReflect] <;> ring

def mirrorPerm (u : Fin 3) : Equiv.Perm Mirror := (mirrorReflect_involutive u).toPerm

@[simp] lemma mirrorPerm_apply (u : Fin 3) (d : Mirror) : mirrorPerm u d = mirrorReflect u d := rfl
@[simp] lemma mirrorPerm_symm_apply (u : Fin 3) (d : Mirror) :
    (mirrorPerm u).symm d = mirrorReflect u d := rfl

lemma mirrorPerm_braid (u : Fin 3) :
    mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u =
      mirrorPerm (u+1) * mirrorPerm u * mirrorPerm (u+1) := by
  apply Equiv.ext
  intro d
  exact mirrorReflect_braid u d

lemma mirrorReflect_side : ∀ u : Fin 3, mirrorReflect u (sideMirror u) = sideMirror u := by decide
lemma mirrorReflect_next : ∀ u : Fin 3, mirrorReflect u (sideMirror (u+1)) = extraMirror u := by decide
lemma mirrorReflect_prev : ∀ u : Fin 3, mirrorReflect (u+1) (sideMirror u) = extraMirror u := by decide
lemma mirrorReflect_extra : ∀ u : Fin 3, mirrorReflect u (extraMirror u) = sideMirror (u+1) := by decide
lemma mirrorReflect_extra_next : ∀ u : Fin 3, mirrorReflect (u+1) (extraMirror u) = sideMirror u := by decide

noncomputable def mirrorBasis (d : Mirror) : Mirror → ℝ := Pi.single d 1

noncomputable def mirrorAut : Equiv.Perm Mirror →* MulAut (Multiplicative (Mirror → ℝ)) where
  toFun p :=
    { toFun := fun ξ => Multiplicative.ofAdd (fun d => ξ.toAdd (p.symm d))
      invFun := fun ξ => Multiplicative.ofAdd (fun d => ξ.toAdd (p d))
      left_inv ξ := by ext d; simp
      right_inv ξ := by ext d; simp
      map_mul' ξ η := rfl }
  map_one' := by ext ξ d; rfl
  map_mul' p q := by ext ξ d; rfl

@[simp] lemma mirrorAut_apply (p : Equiv.Perm Mirror) (ξ : Mirror → ℝ) (d : Mirror) :
    (mirrorAut p (Multiplicative.ofAdd ξ)).toAdd d = ξ (p.symm d) := rfl

lemma mirrorAut_basis (p : Equiv.Perm Mirror) (d : Mirror) :
    mirrorAut p (Multiplicative.ofAdd (mirrorBasis d)) =
      Multiplicative.ofAdd (mirrorBasis (p d)) := by
  ext e
  simp [mirrorBasis, Pi.single_apply, p.symm_apply_eq]

abbrev MirrorAffine := (Multiplicative (Mirror → ℝ)) ⋊[mirrorAut] (Equiv.Perm Mirror)

noncomputable def mirrorGenerator (u : Fin 3) : MirrorAffine :=
  ⟨Multiplicative.ofAdd (mirrorBasis (sideMirror u)), mirrorPerm u⟩

lemma mirrorGenerator_braid (u : Fin 3) :
    mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u =
      mirrorGenerator (u+1) * mirrorGenerator u * mirrorGenerator (u+1) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, mirrorGenerator,
      map_mul, MulAut.mul_apply, mirrorAut_basis, mirrorPerm_apply,
      mirrorReflect_next, mirrorReflect_prev, mirrorReflect_extra, mirrorReflect_extra_next]
    change (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror (u+1)) : Mirror → ℝ) =
      mirrorBasis (sideMirror (u+1)) + mirrorBasis (extraMirror u) + mirrorBasis (sideMirror u)
    abel
  · exact mirrorPerm_braid u

noncomputable def mirrorRepresentation : TriangleGroup →* MirrorAffine :=
  triangleLift mirrorGenerator mirrorGenerator_braid

@[simp] lemma mirrorRepresentation_gen (u : Fin 3) :
    mirrorRepresentation (triangleGen u) = mirrorGenerator u := triangleLift_gen _ _ _

noncomputable def mirrorVector (t : TriangleGroup) : Mirror → ℝ :=
  (mirrorRepresentation t).left.toAdd

noncomputable def mirrorLinear (t : TriangleGroup) : Equiv.Perm Mirror :=
  (mirrorRepresentation t).right

lemma mirrorVector_mul (s t : TriangleGroup) (d : Mirror) :
    mirrorVector (s*t) d = mirrorVector s d + mirrorVector t ((mirrorLinear s).symm d) := by
  simp [mirrorVector, mirrorLinear, map_mul, mirrorAut]

@[simp] lemma mirrorVector_one (d : Mirror) : mirrorVector 1 d = 0 := by simp [mirrorVector]

lemma mirrorVector_generator_abs (u : Fin 3) (d : Mirror) :
    |mirrorVector (triangleGen u) d| ≤ 1 := by
  simp [mirrorVector, mirrorGenerator, mirrorBasis, Pi.single_apply]
  split_ifs <;> norm_num

end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

structure WireSystem (D : Type*) where
  mate : D → D
  mate_inv : Function.Involutive mate
  mate_ne : ∀ d, mate d ≠ d
  pass : D → D
  pass_inv : Function.Involutive pass

namespace WireSystem
variable {D : Type*} (W : WireSystem D)

@[simp] lemma mate_mate (d : D) : W.mate (W.mate d) = d := W.mate_inv d
@[simp] lemma pass_pass (d : D) : W.pass (W.pass d) = d := W.pass_inv d
abbrev Live := {d : D // W.pass d = d}

structure Cut where
  p : D
  moving : W.pass p ≠ p

namespace Cut
variable {W} (K : W.Cut)
abbrev q := W.pass K.p

def Removed (d : D) : Prop := d = K.p ∨ d = K.q
abbrev Kept := {d : D // ¬ K.Removed d}

lemma removed_pass (d : D) : K.Removed (W.pass d) ↔ K.Removed d := by
  constructor <;> intro h <;> rcases h with h | h
  · right
    have := congrArg W.pass h
    simpa using this
  · left
    have := congrArg W.pass h
    simpa using this
  · right
    have := congrArg W.pass h
    simpa using this
  · left
    subst d
    simp [q]

lemma pass_ne (d : D) (hd : K.Removed d) : W.pass d ≠ d := by
  rcases hd with rfl | rfl
  · exact K.moving
  · simpa [q] using K.moving.symm

lemma internal (d : D) (hd : K.Removed d) (hm : K.Removed (W.mate d)) :
    W.mate d = W.pass d := by
  rcases hd with rfl | rfl
  · rcases hm with h | h
    · exact (W.mate_ne K.p h).elim
    · exact h
  · rcases hm with h | h
    · simpa [q] using h
    · exact (W.mate_ne K.q h).elim

lemma mate_pass_outside (d : D) (hd : K.Removed d) (hm : ¬ K.Removed (W.mate d)) :
    ¬ K.Removed (W.mate (W.pass d)) := by
  intro hh
  have h := K.internal (W.pass d) ((K.removed_pass d).2 hd) hh
  simp only [W.pass_pass] at h
  have he := congrArg W.mate h
  simp only [W.mate_mate] at he
  exact hm (he ▸ (K.removed_pass d).2 hd)

noncomputable def splice (d : D) : D := by
  classical
  exact if K.Removed (W.mate d) then W.mate (W.pass (W.mate d)) else W.mate d

lemma splice_inside (d : D) (h : K.Removed (W.mate d)) :
    K.splice d = W.mate (W.pass (W.mate d)) := by simp [splice, h]
lemma splice_outside (d : D) (h : ¬ K.Removed (W.mate d)) :
    K.splice d = W.mate d := by simp [splice, h]

lemma splice_kept (d : D) (hd : ¬ K.Removed d) : ¬ K.Removed (K.splice d) := by
  by_cases hm : K.Removed (W.mate d)
  · rw [K.splice_inside d hm]
    exact K.mate_pass_outside (W.mate d) hm (by simpa using hd)
  · rw [K.splice_outside d hm]
    exact hm

lemma splice_splice (d : D) (hd : ¬ K.Removed d) : K.splice (K.splice d) = d := by
  by_cases hm : K.Removed (W.mate d)
  · rw [K.splice_inside d hm]
    rw [K.splice_inside _ (by simpa using (K.removed_pass (W.mate d)).2 hm)]
    simp
  · rw [K.splice_outside d hm]
    rw [K.splice_outside _ (by simpa using hd)]
    simp

lemma splice_ne (d : D) : K.splice d ≠ d := by
  by_cases hm : K.Removed (W.mate d)
  · rw [K.splice_inside d hm]
    intro h
    have he := congrArg W.mate h
    simp only [W.mate_mate] at he
    exact K.pass_ne (W.mate d) hm he
  · rw [K.splice_outside d hm]
    exact W.mate_ne d

noncomputable def reduced : WireSystem K.Kept where
  mate d := ⟨K.splice d, K.splice_kept d d.property⟩
  mate_inv d := Subtype.ext (K.splice_splice d d.property)
  mate_ne d h := K.splice_ne d (congrArg Subtype.val h)
  pass d := ⟨W.pass d, fun h => d.property ((K.removed_pass d).1 h)⟩
  pass_inv d := Subtype.ext (W.pass_pass d)

lemma live_kept (d : W.Live) : ¬ K.Removed d.val := by
  intro hd
  exact K.pass_ne d hd d.property

def liveEquiv : K.reduced.Live ≃ W.Live where
  toFun d := ⟨d.val.val, congrArg Subtype.val d.property⟩
  invFun d := ⟨⟨d.val,K.live_kept d⟩, Subtype.ext d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def extend (w : K.Kept → ℝ) (d : D) : ℝ := by
  classical
  exact if hd : K.Removed d then
    if hm : K.Removed (W.mate d) then 0 else -w ⟨W.mate d, hm⟩
    else w ⟨d,hd⟩

lemma extend_kept (w : K.Kept → ℝ) (d : K.Kept) : K.extend w d = w d := by
  simp [extend, d.property]

lemma extend_pass_removed (w : K.Kept → ℝ)
    (ha : ∀ d, w (K.reduced.mate d) = -w d) (d : D) (hd : K.Removed d) :
    K.extend w (W.pass d) = -K.extend w d := by
  by_cases hm : K.Removed (W.mate d)
  · have he := K.internal d hd hm
    have he' : W.mate (W.pass d) = d := by rw [← he, W.mate_mate]
    simp [extend, hd, hm, (K.removed_pass d).2 hd, he']
  · have hm' := K.mate_pass_outside d hd hm
    have he : K.reduced.mate ⟨W.mate d,hm⟩ = ⟨W.mate (W.pass d),hm'⟩ := by
      apply Subtype.ext
      change K.splice (W.mate d) = _
      rw [K.splice_inside _ (by simpa using hd), W.mate_mate]
    have hh := ha ⟨W.mate d,hm⟩
    rw [he] at hh
    simp only [extend, dite_eq_left hd, dite_eq_left ((K.removed_pass d).2 hd), dite_eq_right hm,
      dite_eq_right hm', hh, neg_neg]

lemma extend_mate (w : K.Kept → ℝ)
    (ha : ∀ d, w (K.reduced.mate d) = -w d) (d : D) :
    K.extend w (W.mate d) = -K.extend w d := by
  by_cases hd : K.Removed d
  · by_cases hm : K.Removed (W.mate d)
    · simp [extend, hd, hm]
    · simp [extend, hd, hm]
  · by_cases hm : K.Removed (W.mate d)
    · simp [extend, hd, hm]
    · have he : K.reduced.mate ⟨d,hd⟩ = ⟨W.mate d,hm⟩ := by
        exact Subtype.ext (K.splice_outside d hm)
      simpa [extend, hd, hm, he] using ha ⟨d,hd⟩

lemma extend_pass (w : K.Kept → ℝ)
    (ha : ∀ d, w (K.reduced.mate d) = -w d)
    (hb : ∀ d, K.reduced.pass d ≠ d → w (K.reduced.pass d) = -w d)
    (d : D) (hd : W.pass d ≠ d) : K.extend w (W.pass d) = -K.extend w d := by
  by_cases hr : K.Removed d
  · exact K.extend_pass_removed w ha d hr
  · have hr' : ¬ K.Removed (W.pass d) := fun h => hr ((K.removed_pass d).1 h)
    have hb' := hb ⟨d,hr⟩ (fun he => hd (congrArg Subtype.val he))
    simpa [extend, hr, hr', reduced] using hb'

lemma reduced_color {C : Type*} (r : C → C) (hr : Function.Involutive r) (c : D → C)
    (ha : ∀ d, c (W.mate d) = r (c d))
    (hb : ∀ d, W.pass d ≠ d → c (W.pass d) = r (c d)) :
    ∀ d : K.Kept, c (K.reduced.mate d).val = r (c d.val) := by
  intro d
  change c (K.splice d.val) = _
  by_cases hm : K.Removed (W.mate d.val)
  · rw [K.splice_inside _ hm, ha, hb _ (K.pass_ne _ hm), ha, hr]
  · rw [K.splice_outside _ hm, ha]

end Cut

/-- The bivalent parts of a finite graph can be suppressed. In addition to its
boundary matching we retain extension of every antisymmetric edge weight. -/
structure Resolution where
  mate : W.Live → W.Live
  mate_inv : Function.Involutive mate
  mate_ne : ∀ d, mate d ≠ d
  lift : ∀ w : W.Live → ℝ, (∀ d, w (mate d) = -w d) →
    ∃ v : D → ℝ, (∀ d : W.Live, v d.val = w d) ∧
      (∀ d, v (W.mate d) = -v d) ∧
      ∀ d, W.pass d ≠ d → v (W.pass d) = -v d

namespace Resolution
variable {W}

noncomputable def expand (K : W.Cut) (R : K.reduced.Resolution) : W.Resolution where
  mate d := K.liveEquiv (R.mate (K.liveEquiv.symm d))
  mate_inv d := by
    simp only [Equiv.symm_apply_apply]
    rw [R.mate_inv, Equiv.apply_symm_apply]
  mate_ne d h := R.mate_ne (K.liveEquiv.symm d) (by simpa using congrArg K.liveEquiv.symm h)
  lift w hw := by
    let w' : K.reduced.Live → ℝ := fun d => w (K.liveEquiv d)
    have hw' : ∀ d, w' (R.mate d) = -w' d := by
      intro d
      simpa only [w', Equiv.symm_apply_apply] using hw (K.liveEquiv d)
    obtain ⟨v,hv,ha,hb⟩ := R.lift w' hw'
    refine ⟨K.extend v, ?_, K.extend_mate v ha, K.extend_pass v ha hb⟩
    intro d
    have hh := hv (K.liveEquiv.symm d)
    change v ⟨d.val,K.live_kept d⟩ = w' (K.liveEquiv.symm d) at hh
    rw [show K.extend v d.val = v ⟨d.val,K.live_kept d⟩ from K.extend_kept v ⟨d.val,_⟩]
    simpa [w'] using hh

lemma expand_color (K : W.Cut) (R : K.reduced.Resolution)
    {C : Type*} (r : C → C) (c : D → C)
    (hc : ∀ d, c (R.mate d).val.val = r (c d.val.val)) :
    ∀ d, c ((R.expand K).mate d).val = r (c d.val) := by
  intro d
  exact hc (K.liveEquiv.symm d)

noncomputable def of_all_live (h : ∀ d, W.pass d = d) : W.Resolution where
  mate d := ⟨W.mate d.val,h _⟩
  mate_inv d := Subtype.ext (W.mate_mate d.val)
  mate_ne d hd := W.mate_ne d.val (congrArg Subtype.val hd)
  lift w hw := by
    refine ⟨fun d => w ⟨d,h d⟩, fun _ => rfl, fun d => ?_, fun d hd => (hd (h d)).elim⟩
    exact hw ⟨d,h d⟩

end Resolution


/-- Suppression of all bivalent vertices of a finite matching graph, with
reversal-compatible labels and a cocycle lifting property. A closed component
without live ends receives zero in the lift. -/
theorem resolve {C : Type*} (r : C → C) (hr : Function.Involutive r) :
    ∀ (D : Type u) [Fintype D] (W : WireSystem D) (c : D → C),
      (∀ d, c (W.mate d) = r (c d)) →
      (∀ d, W.pass d ≠ d → c (W.pass d) = r (c d)) →
      ∃ R : W.Resolution, ∀ d, c (R.mate d).val = r (c d.val) := by
  suffices hh : ∀ n : ℕ, ∀ (D : Type u) [Fintype D] (W : WireSystem D) (c : D → C),
      Fintype.card D = n →
      (∀ d, c (W.mate d) = r (c d)) →
      (∀ d, W.pass d ≠ d → c (W.pass d) = r (c d)) →
      ∃ R : W.Resolution, ∀ d, c (R.mate d).val = r (c d.val) by
    intro D _ W c ha hb
    exact hh (Fintype.card D) D W c rfl ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    intro D _ W c hn ha hb
    by_cases hp : ∀ d, W.pass d = d
    · refine ⟨Resolution.of_all_live hp, ?_⟩
      intro d
      exact ha d.val
    push Not at hp
    obtain ⟨p,hp⟩ := hp
    let K : W.Cut := ⟨p,hp⟩
    have hcard : Fintype.card K.Kept < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (fun h => h (Or.inl rfl) : ¬ (¬ K.Removed p))
    obtain ⟨R,hR⟩ := ih (Fintype.card K.Kept) hcard K.Kept K.reduced
      (fun d => c d.val) rfl (K.reduced_color r hr c ha hb)
      (fun d hd => hb d.val (fun h => hd (Subtype.ext h)))
    exact ⟨R.expand K, R.expand_color K r c hR⟩

end WireSystem
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0.TriangleMesh

/-- On a collapsed triangular face the two nonconstant sides are paired;
on an uncollapsed face every side is a live terminal. -/
def passIndex (v : Fin 3 → Fin 3) (i : Fin 3) : Fin 3 :=
  if Function.Injective v then i else if v (i+1) ≠ v (i+2) then i+1 else i+2

lemma passIndex_active : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    v (passIndex v i) ≠ v (passIndex v i+1) := by decide

lemma passIndex_involutive : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    passIndex v (passIndex v i) = i := by decide

lemma passIndex_fixed_iff : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    (passIndex v i = i ↔ Function.Injective v) := by decide

lemma passIndex_reverses : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    ¬ Function.Injective v →
    v (passIndex v i) = v (i+1) ∧ v (passIndex v i+1) = v i := by decide

lemma passIndex_cases : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    ¬ Function.Injective v →
    (passIndex v i = i+1 ∧ v (i+2) = v i) ∨
    (passIndex v i = i+2 ∧ v (i+1) = v (i+2)) := by decide

lemma exists_constant_side : ∀ (v : Fin 3 → Fin 3), ¬ Function.Injective v →
    ∃ i, v i = v (i+1) := by decide

lemma passIndex_after_constant : ∀ (v : Fin 3 → Fin 3) (i : Fin 3),
    v i = v (i+1) → v (i+1) ≠ v (i+2) → passIndex v (i+1) = i+2 := by decide

lemma sum_three_rotate (w : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, w j = w i + w (i+1) + w (i+2) := by
  fin_cases i <;> simp [Fin.sum_univ_three, Fin.add_def] <;> ring

lemma sum_collapsed (v : Fin 3 → Fin 3) (w : Fin 3 → ℝ)
    (hf : ¬ Function.Injective v)
    (hz : ∀ i, v i = v (i+1) → w i = 0)
    (hp : ∀ i, v i ≠ v (i+1) → w (passIndex v i) = -w i) :
    ∑ i, w i = 0 := by
  obtain ⟨i,hi⟩ := exists_constant_side v hf
  have h3 : i+2+1 = i := by omega
  rw [sum_three_rotate w i, hz i hi, zero_add]
  by_cases he : v (i+1) = v (i+2)
  · rw [hz (i+1) (by simpa [add_assoc] using he)]
    have hh : v (i+2) = v (i+2+1) := by rw [h3, ← he, hi]
    rw [hz (i+2) hh]
    ring
  · have hh := hp (i+1) (by simpa [add_assoc] using he)
    rw [passIndex_after_constant v i hi he] at hh
    rw [hh]
    ring

variable {F V : Type*} (M : TriangleMesh F V)

/-- Simplicial labels permit a face to map onto an edge or a vertex. The mate
conditions retain the labelled side, not merely its group endpoints. -/
structure SimplicialLabeling where
  cell : F → TargetTriangle
  corner : F → Fin 3 → Fin 3
  vertex : V → TriangleGroup
  vertex_tail : ∀ d, vertex (M.tail d) = (cell d.1).vertex (corner d.1 d.2)
  mate_active : ∀ d,
    (corner (M.mate d).1 (M.mate d).2 ≠ corner (M.mate d).1 ((M.mate d).2+1)) ↔
    (corner d.1 d.2 ≠ corner d.1 (d.2+1))
  mate_compatibility : ∀ d, corner d.1 d.2 ≠ corner d.1 (d.2+1) →
    (cell (M.mate d).1).direction (corner (M.mate d).1 (M.mate d).2)
      (corner (M.mate d).1 ((M.mate d).2+1)) =
    reverseDirection ((cell d.1).direction (corner d.1 d.2) (corner d.1 (d.2+1)))

namespace SimplicialLabeling
variable {M} (L : M.SimplicialLabeling)

def Active (d : F × Fin 3) : Prop := L.corner d.1 d.2 ≠ L.corner d.1 (d.2+1)
def Full (f : F) : Prop := Function.Injective (L.corner f)
abbrev FullFace := {f : F // L.Full f}
abbrev ActiveDart := {d : F × Fin 3 // L.Active d}

noncomputable def wire : WireSystem L.ActiveDart where
  mate d := ⟨M.mate d.val, (L.mate_active d.val).2 d.property⟩
  mate_inv d := Subtype.ext (M.mate_mate d.val)
  mate_ne d h := M.mate_ne d.val (congrArg Subtype.val h)
  pass d := ⟨(d.val.1,passIndex (L.corner d.val.1) d.val.2),
    passIndex_active _ _ d.property⟩
  pass_inv d := Subtype.ext (congrArg (d.val.1,·) (passIndex_involutive _ _ d.property))

lemma full_active (f : L.FullFace) (i : Fin 3) : L.Active (f.val,i) := by
  apply f.property.ne
  intro he
  have := congrArg Fin.val he
  omega

lemma wire_fixed_iff (d : L.ActiveDart) : L.wire.pass d = d ↔ L.Full d.val.1 := by
  constructor
  · intro h
    exact (passIndex_fixed_iff _ _ d.property).1 (congrArg (fun d => d.val.2) h)
  · intro h
    apply Subtype.ext
    exact Prod.ext rfl ((passIndex_fixed_iff _ _ d.property).2 h)

noncomputable def fullDartEquiv : L.wire.Live ≃ L.FullFace × Fin 3 where
  toFun d := (⟨d.val.val.1,(L.wire_fixed_iff d.val).1 d.property⟩,d.val.val.2)
  invFun d := ⟨⟨(d.1.val,d.2),L.full_active d.1 d.2⟩,
    (L.wire_fixed_iff _).2 d.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identify the endpoints of every constant side. `Quot` includes the
reflexive, symmetric, and transitive closure automatically. -/
def ZeroEdge (v w : V) : Prop :=
  ∃ d : F × Fin 3, ¬ L.Active d ∧ M.tail d = v ∧ M.tail (rotate d) = w
abbrev CollapsedVertex := Quot L.ZeroEdge

def qvertex (v : V) : L.CollapsedVertex := Quot.mk _ v

lemma qvertex_zero (d : F × Fin 3) (hd : ¬ L.Active d) :
    L.qvertex (M.tail d) = L.qvertex (M.tail (rotate d)) :=
  Quot.sound ⟨d,hd,rfl,rfl⟩

lemma collapsed_zero (p : V → ℝ) (hp : ∀ d, ¬ L.Active d → p (M.tail d) = p (M.tail (rotate d)))
    {v w : V} (h : L.ZeroEdge v w) : p v = p w := by
  obtain ⟨d,hd,rfl,rfl⟩ := h
  exact hp d hd

lemma vertex_zero {v w : V} (h : L.ZeroEdge v w) : L.vertex v = L.vertex w := by
  obtain ⟨d,hd,rfl,rfl⟩ := h
  rw [L.vertex_tail d, L.vertex_tail (rotate d)]
  have hh : L.corner d.1 d.2 = L.corner d.1 (d.2+1) := not_not.mp hd
  exact congrArg (L.cell d.1).vertex hh

def collapsedLabel : L.CollapsedVertex → TriangleGroup := Quot.lift L.vertex (fun _ _ => L.vertex_zero)

lemma pass_tail_head (d : L.ActiveDart) (hd : L.wire.pass d ≠ d) :
    L.qvertex (M.tail (L.wire.pass d).val) = L.qvertex (M.tail (rotate d.val)) ∧
    L.qvertex (M.tail (rotate (L.wire.pass d).val)) = L.qvertex (M.tail d.val) := by
  have hf : ¬ L.Full d.val.1 := fun h => hd ((L.wire_fixed_iff d).2 h)
  rcases passIndex_cases (L.corner d.val.1) d.val.2 d.property hf with ⟨he,hz⟩ | ⟨he,hz⟩
  · change L.qvertex (M.tail (d.val.1,passIndex _ _)) = _ ∧
      L.qvertex (M.tail (d.val.1,passIndex _ _+1)) = _
    rw [he]
    refine ⟨rfl, ?_⟩
    have hh := L.qvertex_zero (d.val.1,d.val.2+2) (by simpa [Active, show d.val.2+2+1 = d.val.2 by omega] using hz)
    simpa only [rotate_apply, show d.val.2+2+1 = d.val.2 by omega,
      show d.val.2+1+1 = d.val.2+2 by omega] using hh
  · change L.qvertex (M.tail (d.val.1,passIndex _ _)) = _ ∧
      L.qvertex (M.tail (d.val.1,passIndex _ _+1)) = _
    rw [he]
    refine ⟨?_, ?_⟩
    · have hh := L.qvertex_zero (d.val.1,d.val.2+1) (by simpa [Active, add_assoc] using hz)
      simpa only [rotate_apply, show d.val.2+1+1 = d.val.2+2 by omega] using hh.symm
    · rw [show d.val.2+2+1 = d.val.2 by omega]

abbrev WireColor := L.CollapsedVertex × L.CollapsedVertex × LinkDirection

def reverseColor (c : L.WireColor) : L.WireColor := (c.2.1,c.1,reverseDirection c.2.2)

lemma reverseColor_involutive : Function.Involutive L.reverseColor := by
  rintro ⟨x,y,z⟩
  simp only [reverseColor, reverseDirection_reverseDirection]

def wireColor (d : L.ActiveDart) : L.WireColor :=
  (L.qvertex (M.tail d.val), L.qvertex (M.tail (rotate d.val)),
    (L.cell d.val.1).direction (L.corner d.val.1 d.val.2) (L.corner d.val.1 (d.val.2+1)))

lemma wireColor_mate (d : L.ActiveDart) :
    L.wireColor (L.wire.mate d) = L.reverseColor (L.wireColor d) := by
  apply Prod.ext
  · exact congrArg L.qvertex (M.tail_mate d.val)
  · apply Prod.ext
    · exact congrArg L.qvertex (M.tail_rotate_mate d.val)
    · exact L.mate_compatibility d.val d.property

lemma wireColor_pass (d : L.ActiveDart) (hd : L.wire.pass d ≠ d) :
    L.wireColor (L.wire.pass d) = L.reverseColor (L.wireColor d) := by
  obtain ⟨ht,hh⟩ := L.pass_tail_head d hd
  apply Prod.ext ht
  apply Prod.ext hh
  change (L.cell d.val.1).direction (L.corner d.val.1 (passIndex (L.corner d.val.1) d.val.2))
    (L.corner d.val.1 (passIndex (L.corner d.val.1) d.val.2+1)) = _
  obtain ⟨he,hf⟩ := passIndex_reverses (L.corner d.val.1) d.val.2 d.property
    (fun h => hd ((L.wire_fixed_iff d).2 h))
  rw [he,hf]
  exact cellDirection_reverse _ _ _ _ d.property

noncomputable def fullOrder (f : L.FullFace) : CornerOrder :=
  Equiv.ofBijective (L.corner f.val) ((Fintype.bijective_iff_injective_and_card _).2 ⟨f.property,rfl⟩)

@[simp] lemma fullOrder_apply (f : L.FullFace) (i : Fin 3) :
    L.fullOrder f i = L.corner f.val i := rfl

abbrev oldDart (d : L.FullFace × Fin 3) : F × Fin 3 := (d.1.val,d.2)

noncomputable def reducedMate (R : L.wire.Resolution) (d : L.FullFace × Fin 3) : L.FullFace × Fin 3 :=
  L.fullDartEquiv (R.mate (L.fullDartEquiv.symm d))

lemma reducedMate_involutive (R : L.wire.Resolution) : Function.Involutive (L.reducedMate R) := by
  intro d
  simp only [reducedMate, Equiv.symm_apply_apply]
  rw [R.mate_inv, Equiv.apply_symm_apply]

noncomputable def reducedMesh (R : L.wire.Resolution)
    (hc : ∀ d, L.wireColor (R.mate d).val = L.reverseColor (L.wireColor d.val)) :
    TriangleMesh L.FullFace L.CollapsedVertex where
  mate := (L.reducedMate_involutive R).toPerm
  mate_involutive := L.reducedMate_involutive R
  mate_ne d h := R.mate_ne (L.fullDartEquiv.symm d)
    (by
      change L.reducedMate R d = d at h
      simpa only [reducedMate, Equiv.symm_apply_apply] using congrArg L.fullDartEquiv.symm h)
  tail d := L.qvertex (M.tail (L.oldDart d))
  tail_mate d := congrArg Prod.fst (hc (L.fullDartEquiv.symm d))

noncomputable def reducedLabeling (R : L.wire.Resolution)
    (hc : ∀ d, L.wireColor (R.mate d).val = L.reverseColor (L.wireColor d.val)) :
    (L.reducedMesh R hc).Labeling where
  cell f := L.cell f.val
  order := L.fullOrder
  vertex := L.collapsedLabel
  vertex_tail d := L.vertex_tail (L.oldDart d)
  mate_compatibility d := congrArg (fun c : L.WireColor => c.2.2) (hc (L.fullDartEquiv.symm d))

noncomputable def expandWeight (v : L.ActiveDart → ℝ) (d : F × Fin 3) : ℝ := by
  classical
  exact if hd : L.Active d then v ⟨d,hd⟩ else 0

lemma expandWeight_active (v : L.ActiveDart → ℝ) (d : L.ActiveDart) :
    L.expandWeight v d.val = v d := by simp [expandWeight, d.property]

lemma expandWeight_zero (v : L.ActiveDart → ℝ) (d : F × Fin 3) (hd : ¬ L.Active d) :
    L.expandWeight v d = 0 := by simp [expandWeight, hd]

lemma expandWeight_mate (v : L.ActiveDart → ℝ)
    (ha : ∀ d, v (L.wire.mate d) = -v d) (d : F × Fin 3) :
    L.expandWeight v (M.mate d) = -L.expandWeight v d := by
  by_cases hd : L.Active d
  · have hm := (L.mate_active d).2 hd
    rw [L.expandWeight_active v ⟨M.mate d,hm⟩, L.expandWeight_active v ⟨d,hd⟩]
    exact ha ⟨d,hd⟩
  · have hm : ¬ L.Active (M.mate d) := fun h => hd ((L.mate_active d).1 h)
    simp [expandWeight, hd, hm]

lemma expandWeight_collapsed (v : L.ActiveDart → ℝ)
    (hp : ∀ d, L.wire.pass d ≠ d → v (L.wire.pass d) = -v d)
    (f : F) (hf : ¬ L.Full f) : ∑ i, L.expandWeight v (f,i) = 0 := by
  apply sum_collapsed (L.corner f) (fun i => L.expandWeight v (f,i)) hf
  · intro i hi
    exact L.expandWeight_zero v (f,i) (not_not.mpr hi)
  · intro i hi
    have ha := passIndex_active (L.corner f) i hi
    have hh := hp ⟨(f,i),hi⟩ (fun h => hf ((L.wire_fixed_iff _).1 h))
    rw [L.expandWeight_active v ⟨(f,passIndex (L.corner f) i),ha⟩,
      L.expandWeight_active v ⟨(f,i),hi⟩]
    exact hh

lemma expandWeight_full (v : L.ActiveDart → ℝ)
    (w : L.FullFace × Fin 3 → ℝ)
    (hv : ∀ d : L.wire.Live, v d.val = w (L.fullDartEquiv d))
    (d : L.FullFace × Fin 3) : L.expandWeight v (L.oldDart d) = w d := by
  change L.expandWeight v (L.fullDartEquiv.symm d).val.val = _
  rw [L.expandWeight_active, hv, Equiv.apply_symm_apply]

lemma reducedMesh_exact (R : L.wire.Resolution)
    (hcolor : ∀ d, L.wireColor (R.mate d).val = L.reverseColor (L.wireColor d.val))
    (he : M.Exact) : (L.reducedMesh R hcolor).Exact := by
  intro w ha hc
  change ∀ d, w (L.reducedMate R d) = -w d at ha
  let w' : L.wire.Live → ℝ := fun d => w (L.fullDartEquiv d)
  have ha' : ∀ d, w' (R.mate d) = -w' d := by
    intro d
    simpa only [reducedMate, Equiv.symm_apply_apply, w'] using ha (L.fullDartEquiv d)
  obtain ⟨v,hv,hm,hp⟩ := R.lift w' ha'
  have hv' : ∀ d : L.wire.Live, v d.val = w (L.fullDartEquiv d) := hv
  have hface (f : F) : ∑ i, L.expandWeight v (f,i) = 0 := by
    by_cases hf : L.Full f
    · have hh (i) := L.expandWeight_full v w hv' (⟨f,hf⟩,i)
      simpa only [hh] using hc ⟨f,hf⟩
    · exact L.expandWeight_collapsed v hp f hf
  obtain ⟨p,hp⟩ := he (L.expandWeight v) (L.expandWeight_mate v hm) hface
  have hpzero (d : F × Fin 3) (hd : ¬ L.Active d) : p (M.tail d) = p (M.tail (rotate d)) := by
    have hh := hp d
    rw [L.expandWeight_zero v d hd] at hh
    linarith
  let p' : L.CollapsedVertex → ℝ := Quot.lift p (fun _ _ => L.collapsed_zero p hpzero)
  refine ⟨p', fun d => ?_⟩
  have hh := hp (L.oldDart d)
  rw [L.expandWeight_full v w hv' d] at hh
  exact hh

noncomputable def signedSum [Fintype F] (w : TargetTriangle → ℤ) : ℤ := by
  classical
  exact ∑ f : L.FullFace, cornerSign (L.fullOrder f) * w (L.cell f.val)

/-- The sphere-counting dependency including every simplicial degeneracy.
No unproved identification of a pinched diagram with a sphere is used. -/
theorem signed_counts_zero [Fintype F] (he : M.Exact) (w : TargetTriangle → ℤ) :
    L.signedSum w = 0 := by
  classical
  obtain ⟨R,hR⟩ := WireSystem.resolve L.reverseColor L.reverseColor_involutive
    L.ActiveDart L.wire L.wireColor L.wireColor_mate L.wireColor_pass
  exact TriangleMesh.signed_counts_zero w L.FullFace L.CollapsedVertex
    (L.reducedMesh R hR) (L.reducedLabeling R hR) (L.reducedMesh_exact R hR he)

end SimplicialLabeling
end ArtinCAT0.TriangleMesh

namespace ArtinCAT0

lemma mirrorPerm_sq (u : Fin 3) : mirrorPerm u ^ 2 = 1 := by
  apply Equiv.ext
  intro d
  exact mirrorReflect_involutive u d

lemma mirrorGenerator_sq (u : Fin 3) :
    mirrorGenerator u ^ 2 = ⟨Multiplicative.ofAdd (2 • mirrorBasis (sideMirror u)),1⟩ := by
  apply SemidirectProduct.ext
  · simp only [pow_two, SemidirectProduct.mul_left, mirrorGenerator,
      mirrorAut_basis, mirrorPerm_apply, mirrorReflect_side]
    change mirrorBasis (sideMirror u) + mirrorBasis (sideMirror u) =
      (2 : ℕ) • mirrorBasis (sideMirror u)
    simp [two_smul]
  · exact mirrorPerm_sq u

lemma mirrorPerm_delta_sq (u : Fin 3) :
    (mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u) ^ 2 = 1 := by
  have he (i : Fin 3) : mirrorPerm i * mirrorPerm i = 1 := mirrorPerm_sq i
  calc
    _ = mirrorPerm u * mirrorPerm (u+1) * (mirrorPerm u * mirrorPerm u) *
      mirrorPerm (u+1) * mirrorPerm u := by simp only [pow_two, mul_assoc]
    _ = 1 := by rw [he]; simp [mul_assoc, he]

lemma mirrorGenerator_delta (u : Fin 3) :
    mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u =
      ⟨Multiplicative.ofAdd (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
        mirrorBasis (sideMirror (u+1))),
        mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u⟩ := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, mirrorGenerator,
      map_mul, MulAut.mul_apply, mirrorAut_basis, mirrorPerm_apply, mirrorReflect_next,
      mirrorReflect_prev, mirrorReflect_extra]
    rfl
  · rfl

lemma mirrorGenerator_center (u : Fin 3) :
    (mirrorGenerator u * mirrorGenerator (u+1)) ^ 3 =
      ⟨Multiplicative.ofAdd (2 • (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
        mirrorBasis (sideMirror (u+1)))),1⟩ := by
  have hd : (mirrorGenerator u * mirrorGenerator (u+1)) ^ 3 =
      (mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u) ^ 2 := by
    calc
      _ = (mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u) *
        (mirrorGenerator (u+1) * mirrorGenerator u * mirrorGenerator (u+1)) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = _ := by rw [← mirrorGenerator_braid, pow_two]
  rw [hd]
  apply SemidirectProduct.ext
  · rw [pow_two, SemidirectProduct.mul_left, mirrorGenerator_delta]
    change (Multiplicative.ofAdd (mirrorBasis (sideMirror u)) *
      Multiplicative.ofAdd (mirrorBasis (extraMirror u)) *
      Multiplicative.ofAdd (mirrorBasis (sideMirror (u+1)))) *
      mirrorAut (mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u)
        (Multiplicative.ofAdd (mirrorBasis (sideMirror u)) *
        Multiplicative.ofAdd (mirrorBasis (extraMirror u)) *
        Multiplicative.ofAdd (mirrorBasis (sideMirror (u+1)))) = _
    simp only [map_mul, MulAut.mul_apply, mirrorAut_basis, mirrorPerm_apply,
      mirrorReflect_side, mirrorReflect_next, mirrorReflect_prev,
      mirrorReflect_extra, mirrorReflect_extra_next]
    change (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror (u+1))) +
      (mirrorBasis (sideMirror (u+1)) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror u)) =
      (2 : ℕ) • (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror (u+1)))
    simp only [two_smul]
    abel
  · simpa only [pow_two, mirrorGenerator, SemidirectProduct.mul_right]
      using mirrorPerm_delta_sq u

@[simp] lemma mirrorLinear_mul (s t : TriangleGroup) :
    mirrorLinear (s*t) = mirrorLinear s * mirrorLinear t := by
  simp [mirrorLinear]

lemma mirrorVector_inv (t : TriangleGroup) (d : Mirror) :
    mirrorVector t⁻¹ d = -mirrorVector t (mirrorLinear t d) := by
  have h := mirrorVector_mul t t⁻¹ (mirrorLinear t d)
  simp only [mul_inv_cancel, mirrorVector_one, Equiv.symm_apply_apply] at h
  linarith

lemma mirrorVector_bounded (t : TriangleGroup) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d, |mirrorVector t d| ≤ C := by
  let H : Subgroup TriangleGroup :=
    { carrier := {t | ∃ C : ℝ, 0 ≤ C ∧ ∀ d, |mirrorVector t d| ≤ C}
      one_mem' := ⟨0,le_rfl,by intro d; simp⟩
      mul_mem' := by
        rintro a b ⟨A,hA,ha⟩ ⟨B,hB,hb⟩
        refine ⟨A+B,add_nonneg hA hB,fun d => ?_⟩
        rw [mirrorVector_mul]
        exact (abs_add_le _ _).trans (add_le_add (ha _) (hb _))
      inv_mem' := by
        rintro a ⟨A,hA,ha⟩
        exact ⟨A,hA,fun d => by rw [mirrorVector_inv,abs_neg]; exact ha _⟩ }
  have hh : ∀ i : Fin 3, (PresentedGroup.of i : TriangleGroup) ∈ H := by
    intro i
    exact ⟨1,by norm_num, mirrorVector_generator_abs i⟩
  exact PresentedGroup.generated_by triangleRelators H hh t

end ArtinCAT0

namespace ArtinCAT0
section OrbitControl
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

lemma orbit_uniformly_dense (hG : GeometricAction G X) (y : X) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p : X, ∃ s : G, dist p (s • y) ≤ R := by
  obtain ⟨K,hK,hcover⟩ := hG.2.2.2
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall y
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro p
  obtain ⟨s,k,hk,rfl⟩ := hcover p
  refine ⟨s, ?_⟩
  rw [(hG.2.1 s).dist_eq]
  exact (hR hk).trans (le_max_left _ _)

/-- A local bound on an orbit becomes a coarse linear global bound. The
constant two only avoids a special case for zero length geodesics. -/
lemma orbit_chain_control (hG : GeometricAction G X) (y : X)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hdense : ∀ p : X, ∃ s : G, dist p (s • y) ≤ R)
    (f : G → ℝ)
    (hlocal : ∀ s t : G, dist (s • y) (t • y) ≤ 2*R+1 → |f t-f s| ≤ C)
    (s t : G) : |f t-f s| ≤ 2*C*(1+dist (s • y) (t • y)) := by
  classical
  let L : ℝ := dist (s • y) (t • y)
  have hL : 0 ≤ L := dist_nonneg
  let N : ℕ := ⌈L⌉₊ + 1
  have hN : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLN : L ≤ (N : ℝ) := (Nat.le_ceil L).trans (by simp [N])
  have hNL : (N : ℝ) ≤ L+2 := by
    have h := Nat.ceil_lt_add_one hL
    dsimp [N]
    push_cast
    linarith
  obtain ⟨γ,hγ⟩ := hG.1.1 (s • y) (t • y)
  choose a ha using hdense
  let q : ℕ → G := fun i => if i = 0 then s else if i = N then t else a (γ (i/N))
  have hq0 : q 0 = s := by simp [q]
  have hqN : q N = t := by simp [q, Nat.ne_of_gt hN]
  have hq (i : ℕ) : dist (γ (i/N)) (q i • y) ≤ R := by
    by_cases hi : i = 0
    · subst i; simpa [q,hγ.1] using hR
    by_cases hiN : i = N
    · subst i
      simpa [q, Nat.ne_of_gt hN, ne_of_gt hNr, hγ.2.1] using hR
    · simpa [q,hi,hiN] using ha (γ (i/N))
  have hstep (i : ℕ) (hi : i < N) : dist (q i • y) (q (i+1) • y) ≤ 2*R+1 := by
    have hi0 : 0 ≤ (i : ℝ)/(N : ℝ) := div_nonneg (by positivity) hNr.le
    have hi1 : (i : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hi.le)
    have hj0 : 0 ≤ ((i+1 : ℕ) : ℝ)/(N : ℝ) := div_nonneg (by positivity) hNr.le
    have hj1 : ((i+1 : ℕ) : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hi)
    have hdist : dist (γ (i/N)) (γ ((i+1 : ℕ)/N)) ≤ 1 := by
      rw [hγ.2.2 _ ⟨hi0,hi1⟩ _ ⟨hj0,hj1⟩]
      change |(i : ℝ)/(N : ℝ) - ((i+1 : ℕ) : ℝ)/(N : ℝ)| * L ≤ 1
      rw [show (i : ℝ)/(N : ℝ) - ((i+1 : ℕ) : ℝ)/(N : ℝ) = -(1/(N : ℝ)) by push_cast; ring,
        abs_neg, abs_of_nonneg (by positivity)]
      simpa [div_eq_mul_inv, mul_comm] using (div_le_one hNr).mpr hLN
    have htri := dist_triangle4 (q i • y) (γ (i/N))
      (γ ((i+1 : ℕ)/N)) (q (i+1) • y)
    have hqi := hq i
    rw [dist_comm] at hqi
    linarith [hq (i+1)]
  have hsum : ∀ i ≤ N, |f (q i)-f (q 0)| ≤ (i : ℝ)*C := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have ih' := ih (by omega)
      have hs := hlocal (q i) (q (i+1)) (hstep i (by omega))
      have ht := abs_sub_le (f (q (i+1))) (f (q i)) (f (q 0))
      push_cast
      linarith
  have hlast := hsum N le_rfl
  rw [hqN,hq0] at hlast
  calc
    _ ≤ (N : ℝ)*C := hlast
    _ ≤ (L+2)*C := mul_le_mul_of_nonneg_right hNL hC
    _ ≤ 2*C*(1+L) := by nlinarith

end OrbitControl
end ArtinCAT0

namespace ArtinCAT0
namespace RayIndex

noncomputable section

abbrev Point := ℝ × ℝ

def det (p q : Point) : ℝ := p.1 * q.2 - q.1 * p.2

def upward (p q : Point) : ℤ := if p.2 ≤ 0 ∧ 0 < q.2 ∧ 0 < det p q then 1 else 0

def edge (p q : Point) : ℤ := upward p q - upward q p

def above (p : Point) : ℤ := if 0 < p.2 then 1 else 0

@[simp] lemma edge_self (p : Point) : edge p p = 0 := sub_self _
lemma edge_reverse (p q : Point) : edge q p = -edge p q := by unfold edge; ring

lemma det_pos_of_cross_right {p q : Point} (hp : 0 < p.1) (hq : 0 < q.1)
    (hy : p.2 ≤ 0) (hy' : 0 < q.2) : 0 < det p q := by
  have h₁ := mul_pos hp hy'
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hq.le hy
  dsimp [det]
  linarith

lemma det_neg_of_cross_left {p q : Point} (hp : p.1 < 0) (hq : q.1 < 0)
    (hy : p.2 ≤ 0) (hy' : 0 < q.2) : det p q < 0 := by
  have h₁ := mul_neg_of_neg_of_pos hp hy'
  have h₂ := mul_nonneg_of_nonpos_of_nonpos hq.le hy
  dsimp [det]
  linarith

lemma edge_right {p q : Point} (hp : 0 < p.1) (hq : 0 < q.1) :
    edge p q = above q - above p := by
  by_cases hy : p.2 ≤ 0 <;> by_cases hy' : q.2 ≤ 0
  · simp [edge, upward, above, not_lt.mpr hy, not_lt.mpr hy']
  · have hq' := lt_of_not_ge hy'
    have hdet := det_pos_of_cross_right hp hq hy hq'
    simp [edge, upward, above, hy, hy', not_lt.mpr hy, hq', hdet]
  · have hp' := lt_of_not_ge hy
    have hdet := det_pos_of_cross_right hq hp hy' hp'
    simp [edge, upward, above, hy, hy', not_lt.mpr hy', hp', hdet]
  · simp [edge, upward, above, hy, hy', lt_of_not_ge hy, lt_of_not_ge hy']

lemma edge_left {p q : Point} (hp : p.1 < 0) (hq : q.1 < 0) : edge p q = 0 := by
  have h₁ : ¬ (p.2 ≤ 0 ∧ 0 < q.2 ∧ 0 < det p q) := by
    rintro ⟨hy,hy',hd⟩
    exact (det_neg_of_cross_left hp hq hy hy').not_gt hd
  have h₂ : ¬ (q.2 ≤ 0 ∧ 0 < p.2 ∧ 0 < det q p) := by
    rintro ⟨hy,hy',hd⟩
    exact (det_neg_of_cross_left hq hp hy hy').not_gt hd
  simp [edge, upward, h₁, h₂]

lemma edge_high {p q : Point} (hp : 0 < p.2) (hq : 0 < q.2) : edge p q = 0 := by
  simp [edge, upward, hp.not_ge, hq.not_ge]

lemma edge_low {p q : Point} (hp : p.2 ≤ 0) (hq : q.2 ≤ 0) : edge p q = 0 := by
  simp [edge, upward, hp.not_gt, hq.not_gt]

def face (p : Fin 3 → Point) : ℤ := ∑ i, edge (p i) (p (i+1))

lemma face_eq (p : Fin 3 → Point) :
    face p = edge (p 0) (p 1) + edge (p 1) (p 2) + edge (p 2) (p 0) := by
  rw [face, Fin.sum_univ_three]
  rfl

lemma face_right (p : Fin 3 → Point) (hp : ∀ i, 0 < (p i).1) : face p = 0 := by
  rw [face_eq]
  rw [edge_right (hp 0) (hp 1), edge_right (hp 1) (hp 2), edge_right (hp 2) (hp 0)]
  ring

lemma face_left (p : Fin 3 → Point) (hp : ∀ i, (p i).1 < 0) : face p = 0 := by
  simp [face, edge_left (hp _) (hp _)]

lemma face_high (p : Fin 3 → Point) (hp : ∀ i, 0 < (p i).2) : face p = 0 := by
  simp [face, edge_high (hp _) (hp _)]

lemma face_low (p : Fin 3 → Point) (hp : ∀ i, (p i).2 ≤ 0) : face p = 0 := by
  simp [face, edge_low (hp _) (hp _)]

lemma corner_order_cases : ∀ p : CornerOrder,
    (p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 2) ∨ (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 0) ∨
    (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 1) ∨ (p 0 = 0 ∧ p 1 = 2 ∧ p 2 = 1) ∨
    (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 2) ∨ (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 0) := by decide

lemma face_permute (p : Fin 3 → Point) (e : CornerOrder) :
    face (p ∘ e) = cornerSign e * face p := by
  rcases corner_order_cases e with h|h|h|h|h|h <;>
    rcases h with ⟨h₀,h₁,h₂⟩ <;>
    simp only [face_eq, Function.comp_apply, cornerSign, h₀,h₁,h₂] <;>
    norm_num [Fin.add_def, Fin.ext_iff] <;> unfold edge <;> ring

lemma face_collapsed (p : Fin 3 → Point) (v : Fin 3 → Fin 3) (hv : ¬ Function.Injective v) :
    face (p ∘ v) = 0 := by
  obtain ⟨i,hi⟩ := TriangleMesh.exists_constant_side v hv
  have hs : face (p ∘ v) =
      edge (p (v i)) (p (v (i+1))) + edge (p (v (i+1))) (p (v (i+2))) +
        edge (p (v (i+2))) (p (v i)) := by
    fin_cases i <;> simp [face_eq, Function.comp_apply, Fin.add_def] <;> ring
  rw [hs, hi]
  unfold edge
  ring

/-- A nonzero local edge-index sum forces the coordinate bounding box to meet
both axes. This avoids a separate topological winding-number API. -/
lemma face_bbox (p : Fin 3 → Point) (hp : face p ≠ 0) :
    (∃ i, (p i).1 ≤ 0) ∧ (∃ i, 0 ≤ (p i).1) ∧
      (∃ i, (p i).2 ≤ 0) ∧ (∃ i, 0 < (p i).2) := by
  constructor
  · by_contra h
    push Not at h
    exact hp (face_right p h)
  constructor
  · by_contra h
    push Not at h
    exact hp (face_left p h)
  constructor
  · by_contra h
    push Not at h
    exact hp (face_high p h)
  · by_contra h
    push Not at h
    exact hp (face_low p h)

lemma face_local {p : Fin 3 → Point} (hp : face p ≠ 0) (x : Point) {ε : ℝ}
    (hx : ∀ i, |(p i).1 - x.1| < ε ∧ |(p i).2 - x.2| < ε) :
    |x.1| < ε ∧ |x.2| < ε := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩,⟨l,hl⟩⟩ := face_bbox p hp
  have hix := abs_lt.mp (hx i).1
  have hjx := abs_lt.mp (hx j).1
  have hkx := abs_lt.mp (hx k).2
  have hlx := abs_lt.mp (hx l).2
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith

section Mesh
variable {F V : Type*} [Fintype F] (M : TriangleMesh F V)

omit [Fintype F] in
lemma edge_mate (p : V → Point) (d : F × Fin 3) :
    edge (p (M.tail (M.mate d))) (p (M.tail (TriangleMesh.rotate (M.mate d)))) =
      -edge (p (M.tail d)) (p (M.tail (TriangleMesh.rotate d))) := by
  rw [M.tail_mate, M.tail_rotate_mate]
  exact edge_reverse _ _

/-- Finite Stokes cancellation on any union of faces; no manifold hypotheses
are needed because the oriented edge matching is explicit. -/
lemma patch_boundary_sum (P : F → Prop) [DecidablePred P] (p : V → Point) :
    (∑ f, if P f then face (fun i => p (M.tail (f,i))) else 0) =
      ∑ d : F × Fin 3, if P d.1 ∧ ¬ P (M.mate d).1 then
        edge (p (M.tail d)) (p (M.tail (TriangleMesh.rotate d))) else 0 := by
  classical
  let w (d : F × Fin 3) := edge (p (M.tail d)) (p (M.tail (TriangleMesh.rotate d)))
  let interior (d : F × Fin 3) := if P d.1 ∧ P (M.mate d).1 then w d else 0
  have ha (d) : interior (M.mate d) = -interior d := by
    dsimp [interior]
    rw [M.mate_mate]
    by_cases hf : P d.1 <;> by_cases hg : P (M.mate d).1 <;> simp only [hf,hg,and_self,ite_true,and_false,and_true,ite_false,neg_zero]
    exact edge_mate M p d
  have hz : ∑ d, interior d = 0 := by
    have he := Equiv.sum_comp M.mate interior
    simp only [ha, Finset.sum_neg_distrib] at he
    omega
  have he : (∑ f, if P f then face (fun i => p (M.tail (f,i))) else 0) =
      ∑ d : F × Fin 3, if P d.1 then w d else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : P f <;> simp [hf,face,w]
  rw [he]
  have hd (d : F × Fin 3) : (if P d.1 then w d else 0) =
      interior d + (if P d.1 ∧ ¬ P (M.mate d).1 then w d else 0) := by
    by_cases hf : P d.1 <;> by_cases hg : P (M.mate d).1 <;> simp [hf,hg,interior]
  simp only [hd, Finset.sum_add_distrib, hz, zero_add]
  rfl

variable (L : M.SimplicialLabeling) (J : TriangleGroup → Point)

def occurrence (f : F) : ℤ := face (fun i => J (L.vertex (M.tail (f,i))))

def target (c : TargetTriangle) : ℤ := face (J ∘ c.vertex)

omit [Fintype F] in
lemma occurrence_full (f : L.FullFace) :
    occurrence M L J f.val = cornerSign (L.fullOrder f) * target J (L.cell f.val) := by
  unfold occurrence target
  conv_lhs => arg 1; intro i; rw [L.vertex_tail]
  exact face_permute (J ∘ (L.cell f.val).vertex) (L.fullOrder f)

omit [Fintype F] in
lemma occurrence_collapsed (f : F) (hf : ¬ L.Full f) : occurrence M L J f = 0 := by
  unfold occurrence
  conv_lhs => arg 1; intro i; rw [L.vertex_tail]
  exact face_collapsed (J ∘ (L.cell f).vertex) (L.corner f) hf

theorem localized_zero (he : M.Exact) (P : F → Prop) [DecidablePred P]
    (hloc : ∀ f g : F, P f → occurrence M L J f ≠ 0 → L.cell f = L.cell g →
      L.Full g → P g) :
    (∑ f, if P f then occurrence M L J f else 0) = 0 := by
  classical
  let S (c : TargetTriangle) := ∃ f, P f ∧ occurrence M L J f ≠ 0 ∧ L.cell f = c
  let w (c : TargetTriangle) := if S c then target J c else 0
  have hfull (f : L.FullFace) :
      (if P f.val then occurrence M L J f.val else 0) =
        cornerSign (L.fullOrder f) * w (L.cell f.val) := by
    by_cases hf : P f.val
    · rw [ite_eq_left hf]
      by_cases hz : occurrence M L J f.val = 0
      · by_cases hs : S (L.cell f.val)
        · simpa only [w, ite_eq_left hs] using occurrence_full M L J f
        · simp [w,hs,hz]
      · have hs : S (L.cell f.val) := ⟨f.val,hf,hz,rfl⟩
        simpa only [w, ite_eq_left hs] using occurrence_full M L J f
    · have hs : ¬ S (L.cell f.val) := by
        rintro ⟨g,hg,hz,hcell⟩
        exact hf (hloc g f.val hg hz hcell f.property)
      simp [hf,w,hs]
  have hzero : (∑ f : {f : F // ¬ L.Full f},
      if P f.val then occurrence M L J f.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    simp [occurrence_collapsed M L J f.val f.property]
  rw [← Fintype.sum_subtype_add_sum_subtype L.Full
    (fun f => if P f then occurrence M L J f else 0), hzero, add_zero]
  simp_rw [hfull]
  exact L.signed_counts_zero he w

end Mesh
end
end RayIndex
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0

/-- A triangular disk may have unpaired boundary darts. No topological theorem
is hidden in this interface: exactness is required and subsequently proved for
the explicit grid disks used in the controlled-diagram construction. -/
structure TrianglePatch (F V : Type*) where
  mate : Equiv.Perm (F × Fin 3)
  mate_involutive : Function.Involutive mate
  tail : F × Fin 3 → V
  tail_mate : ∀ d, mate d ≠ d → tail (mate d) = tail (d.1,d.2+1)

namespace TrianglePatch
variable {F V : Type*} (M : TrianglePatch F V)

def Boundary (d : F × Fin 3) : Prop := M.mate d = d

def Exact : Prop :=
  ∀ w : F × Fin 3 → ℝ,
    (∀ d, ¬ M.Boundary d → w (M.mate d) = -w d) →
    (∀ f, ∑ i : Fin 3, w (f,i) = 0) →
    ∃ p : V → ℝ, ∀ d, w d = p (M.tail (d.1,d.2+1)) - p (M.tail d)

@[simp] lemma mate_mate (d : F × Fin 3) : M.mate (M.mate d) = d := M.mate_involutive d

lemma tail_rotate_mate (d : F × Fin 3) (hd : ¬ M.Boundary d) :
    M.tail ((M.mate d).1,(M.mate d).2+1) = M.tail d := by
  rw [← M.tail_mate (M.mate d) (by intro h; exact hd (M.mate.injective h)), M.mate_mate]

end TrianglePatch

namespace GridDisk
variable (H N : ℕ) [NeZero N]

abbrev Face := (Fin (H+1) × Fin N × Bool) ⊕ Fin N
abbrev Vertex := (Fin (H+2) × Fin N) ⊕ Unit
abbrev A (r : Fin (H+1)) (i : Fin N) : Face H N := Sum.inl (r,i,false)
abbrev B (r : Fin (H+1)) (i : Fin N) : Face H N := Sum.inl (r,i,true)
abbrev C (i : Fin N) : Face H N := Sum.inr i

def mateFun : Face H N × Fin 3 → Face H N × Fin 3
  | (Sum.inl (r,i,false),k) =>
      if k = 0 then
        if h : r.val+1 < H+1 then (B H N ⟨r.val+1,h⟩ i,1) else (A H N r i,0)
      else if k = 1 then (B H N r (i+1),2) else (B H N r i,0)
  | (Sum.inl (r,i,true),k) =>
      if k = 0 then (A H N r i,2)
      else if k = 1 then
        if h : r.val = 0 then (C H N i,0) else (A H N ⟨r.val-1,by omega⟩ i,0)
      else (A H N r (i-1),1)
  | (Sum.inr i,k) =>
      if k = 0 then (B H N 0 i,1)
      else if k = 1 then (C H N (i+1),2) else (C H N (i-1),1)

lemma mateFun_involutive : Function.Involutive (mateFun H N) := by
  rintro ⟨f,k⟩
  rcases f with ⟨r,i,b⟩ | i
  · cases b <;> fin_cases k <;> simp only [mateFun]
    all_goals split_ifs <;> simp_all [A,B]
    all_goals split_ifs <;> simp_all only [Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff, Fin.val_zero]
    all_goals try simp only [and_true]
    all_goals omega
  · fin_cases k <;> simp [mateFun,B,C]

def tail : Face H N × Fin 3 → Vertex H N
  | (Sum.inl (r,i,false),k) =>
      if k = 0 then Sum.inl (r.succ,i)
      else if k = 1 then Sum.inl (r.succ,i+1) else Sum.inl (r.castSucc,i+1)
  | (Sum.inl (r,i,true),k) =>
      if k = 0 then Sum.inl (r.succ,i)
      else if k = 1 then Sum.inl (r.castSucc,i+1) else Sum.inl (r.castSucc,i)
  | (Sum.inr i,k) =>
      if k = 0 then Sum.inl (0,i)
      else if k = 1 then Sum.inl (0,i+1) else Sum.inr ()

lemma tail_mateFun (d : Face H N × Fin 3) (hd : mateFun H N d ≠ d) :
    tail H N (mateFun H N d) = tail H N (d.1,d.2+1) := by
  rcases d with ⟨f,k⟩
  rcases f with ⟨r,i,b⟩ | i
  · cases b <;> fin_cases k <;> simp only [mateFun] at hd ⊢
    all_goals split_ifs at hd ⊢ <;> simp_all [tail,A,B,C,Fin.add_def]
    all_goals simp only [Fin.ext_iff,Fin.val_zero,Fin.val_succ,Fin.val_castSucc] at *
    all_goals omega
  · fin_cases k <;> simp [mateFun,tail,B,C,Fin.add_def]

def patch : TrianglePatch (Face H N) (Vertex H N) where
  mate := ⟨mateFun H N, mateFun H N, mateFun_involutive H N, mateFun_involutive H N⟩
  mate_involutive := mateFun_involutive H N
  tail := tail H N
  tail_mate := tail_mateFun H N

noncomputable def upper (w : Face H N × Fin 3 → ℝ) (r : Fin (H+1)) (i : Fin N) : ℝ :=
  if h : r.val = 0 then w (C H N i,0) else w (A H N ⟨r.val-1,by omega⟩ i,0)

noncomputable def potential (w : Face H N × Fin 3 → ℝ) : ℕ → Fin N → ℝ
  | 0,i => w (C H N i,2)
  | k+1,i => potential w k i + if h : k < H+1 then w (B H N ⟨k,h⟩ i,2) else 0

omit [NeZero N] in
lemma potential_succ (w : Face H N × Fin 3 → ℝ) (r : Fin (H+1)) (i : Fin N) :
    potential H N w (r.val+1) i = potential H N w r.val i + w (B H N r i,2) := by
  simp [potential,r.isLt]

lemma cocycle_relations (w : Face H N × Fin 3 → ℝ)
    (ha : ∀ d, ¬ (patch H N).Boundary d → w ((patch H N).mate d) = -w d) :
    (∀ r i, w (A H N r i,1) = -w (B H N r (i+1),2)) ∧
    (∀ r i, w (A H N r i,2) = -w (B H N r i,0)) ∧
    (∀ r i, w (B H N r i,1) = -upper H N w r i) ∧
    (∀ i, w (C H N i,1) = -w (C H N (i+1),2)) := by
  have hh (d) (hd : mateFun H N d ≠ d) : w (mateFun H N d) = -w d := ha d hd
  constructor
  · intro r i
    have h := hh (A H N r i,1) (by simp [mateFun,A,B])
    simp only [mateFun,A,B,Fin.isValue,Fin.reduceEq,ite_false,ite_true] at h
    linarith
  constructor
  · intro r i
    have h := hh (A H N r i,2) (by simp [mateFun,A,B])
    simp only [mateFun,A,B,Fin.isValue,Fin.reduceEq,ite_false] at h
    linarith
  constructor
  · intro r i
    have h := hh (B H N r i,1) (by simp [mateFun,A,B,C]; split_ifs <;> simp)
    by_cases hr : r.val = 0 <;> simp [mateFun,A,B,C,hr,upper] at h ⊢ <;> linarith
  · intro i
    have h := hh (C H N i,1) (by simp [mateFun,C])
    simp only [mateFun,C,Fin.isValue,Fin.reduceEq,ite_false,ite_true] at h
    linarith

/-- Exactness of the explicit capped cylindrical disk. The proof constructs a
potential by integrating vertically downward from the cap; the square and cap
relations verify every horizontal edge. -/
theorem exact : (patch H N).Exact := by
  intro w ha hc
  obtain ⟨hA₁,hA₂,hB₁,hC₁⟩ := cocycle_relations H N w ha
  have hc' (f) : w (f,0) + w (f,1) + w (f,2) = 0 := by
    simpa only [Fin.sum_univ_three] using hc f
  have hcap (i) : w (C H N i,0) = potential H N w 0 (i+1) - potential H N w 0 i := by
    have h := hc' (C H N i)
    rw [hC₁] at h
    simpa only [potential] using (show w (C H N i,0) = w (C H N (i+1),2)-w (C H N i,2) by linarith)
  have hstep (r : Fin (H+1))
      (hu : ∀ i, upper H N w r i = potential H N w r.val (i+1) - potential H N w r.val i) :
      ∀ i, w (A H N r i,0) = potential H N w (r.val+1) (i+1) - potential H N w (r.val+1) i := by
    intro i
    have hA := hc' (A H N r i)
    have hB := hc' (B H N r i)
    rw [hA₁,hA₂] at hA
    rw [hB₁,hu] at hB
    rw [potential_succ,potential_succ]
    linarith
  have hrow : ∀ k, ∀ hk : k < H+1, ∀ i,
      w (A H N ⟨k,hk⟩ i,0) = potential H N w (k+1) (i+1) - potential H N w (k+1) i := by
    intro k
    induction k with
    | zero =>
      intro hk
      apply hstep
      intro i
      simpa [upper] using hcap i
    | succ k ih =>
      intro hk
      apply hstep
      intro i
      simpa [upper] using ih (by omega) i
  have hu (r : Fin (H+1)) (i : Fin N) :
      upper H N w r i = potential H N w r.val (i+1) - potential H N w r.val i := by
    by_cases hr : r.val = 0
    · simpa [upper,hr] using hcap i
    · simpa [upper,hr,Nat.sub_add_cancel (by omega : 1 ≤ r.val)] using
        hrow (r.val-1) (by omega) i
  let p : Vertex H N → ℝ := fun v => match v with
    | Sum.inl (r,i) => potential H N w r.val i
    | Sum.inr _ => 0
  refine ⟨p, ?_⟩
  rintro ⟨f,k⟩
  change w (f,k) = p (tail H N (f,k+1)) - p (tail H N (f,k))
  rcases f with ⟨r,i,b⟩ | i
  · have hA := hc' (A H N r i)
    have hB := hc' (B H N r i)
    have hb₁ := hB₁ r i
    rw [hu] at hb₁
    have ha₁ := hA₁ r i
    have ha₂ := hA₂ r i
    have ha₀ := hrow r.val r.isLt i
    have hp := potential_succ H N w r i
    have hp' := potential_succ H N w r (i+1)
    cases b
    · fin_cases k
      · change w (A H N r i,0) = potential H N w (r.val+1) (i+1) - potential H N w (r.val+1) i
        exact ha₀
      · change w (A H N r i,1) = potential H N w r.val (i+1) - potential H N w (r.val+1) (i+1)
        linarith
      · change w (A H N r i,2) = potential H N w (r.val+1) i - potential H N w r.val (i+1)
        linarith
    · fin_cases k
      · change w (B H N r i,0) = potential H N w r.val (i+1) - potential H N w (r.val+1) i
        linarith
      · change w (B H N r i,1) = potential H N w r.val i - potential H N w r.val (i+1)
        linarith
      · change w (B H N r i,2) = potential H N w (r.val+1) i - potential H N w r.val i
        linarith
  · have h₀ := hcap i
    have h₁ := hC₁ i
    fin_cases k
    · change w (C H N i,0) = potential H N w 0 (i+1) - potential H N w 0 i
      exact h₀
    · change w (C H N i,1) = 0 - w (C H N (i+1),2)
      simpa using h₁
    · change w (C H N i,2) = w (C H N i,2) - 0
      ring

end GridDisk
end ArtinCAT0

namespace ArtinCAT0

namespace TrianglePatch
variable {A U : Type*}

/-- Three marked, equally subdivided sides of a triangular patch. The marks
are combinatorial; the vertices and faces need not be mapped injectively. -/
structure Sides (P : TrianglePatch A U) (K : ℕ) where
  dart : Fin 3 × Fin K → A × Fin 3
  point : Fin 3 × Fin (K+1) → U
  dart_injective : Function.Injective dart
  fixed : ∀ e, P.Boundary (dart e)
  complete : ∀ d, P.Boundary d → ∃ e, dart e = d
  tail : ∀ i j, P.tail (dart (i,j)) = point (i,j.castSucc)
  head : ∀ i j, P.tail ((dart (i,j)).1,(dart (i,j)).2+1) = point (i,j.succ)
  ends : ∀ i, point (i,Fin.last K) = point (i+1,0)

lemma boundary_mate (P : TrianglePatch A U) (d : A × Fin 3) :
    P.Boundary (P.mate d) ↔ P.Boundary d := by
  unfold Boundary
  rw [P.mate_mate]
  exact eq_comm

namespace Sides
variable {P : TrianglePatch A U} {K : ℕ} [NeZero K] (S : P.Sides K)
noncomputable def index (d : A × Fin 3) : Fin 3 × Fin K := by
  classical
  exact if h : P.Boundary d then (S.complete d h).choose else (0,0)

@[simp] lemma index_dart (e : Fin 3 × Fin K) : S.index (S.dart e) = e := by
  classical
  apply S.dart_injective
  simp only [index,dite_eq_left (S.fixed e)]
  exact (S.complete _ (S.fixed e)).choose_spec

lemma dart_index (d : A × Fin 3) (h : P.Boundary d) : S.dart (S.index d) = d := by
  classical
  simp only [index,dite_eq_left h]
  exact (S.complete d h).choose_spec

end Sides
end TrianglePatch

lemma reverse_chain_difference {K : ℕ} (a b : Fin (K+1) → ℝ)
    (h : ∀ j : Fin K, a j.succ - a j.castSucc = b j.rev.castSucc - b j.rev.succ) :
    ∀ j, a j - a 0 = b j.rev - b (Fin.last K) := by
  intro j
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    have hh := h j
    rw [Fin.rev_castSucc] at ih
    rw [Fin.rev_succ]
    linarith

namespace TriangleMesh
variable {F V A U : Type*} (M : TriangleMesh F V) (P : TrianglePatch A U)
  {K : ℕ} [NeZero K] (S : P.Sides K)

namespace Replacement

noncomputable def mateFun (d : (F × A) × Fin 3) : (F × A) × Fin 3 := by
  classical
  exact if h : P.Boundary (d.1.2,d.2) then
    let e := S.index (d.1.2,d.2)
    let m := M.mate (d.1.1,e.1)
    let t := S.dart (m.2,e.2.rev)
    ((m.1,t.1),t.2)
  else
    let t := P.mate (d.1.2,d.2)
    ((d.1.1,t.1),t.2)

@[simp] lemma mate_boundary (f : F) (i : Fin 3) (j : Fin K) :
    mateFun M P S ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) =
      (((M.mate (f,i)).1, (S.dart ((M.mate (f,i)).2,j.rev)).1),
        (S.dart ((M.mate (f,i)).2,j.rev)).2) := by
  classical
  simp only [mateFun,Prod.mk.eta,S.fixed,dite_eq_left,S.index_dart]

lemma mate_internal (f : F) (d : A × Fin 3) (hd : ¬ P.Boundary d) :
    mateFun M P S ((f,d.1),d.2) = ((f,(P.mate d).1),(P.mate d).2) := by
  classical
  simp [mateFun,hd]

lemma mateFun_involutive : Function.Involutive (mateFun M P S) := by
  rintro ⟨⟨f,a⟩,k⟩
  by_cases hd : P.Boundary (a,k)
  · obtain ⟨⟨i,j⟩,he⟩ := S.complete _ hd
    have hd' : ((f,a),k) = ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) := by rw [he]
    rw [hd',mate_boundary,mate_boundary,M.mate_mate,Fin.rev_rev]
  · rw [mate_internal M P S f (a,k) hd,
      mate_internal M P S f (P.mate (a,k)) (by simpa only [P.boundary_mate] using hd),
      P.mate_mate]

lemma mateFun_ne (d : (F × A) × Fin 3) : mateFun M P S d ≠ d := by
  rcases d with ⟨⟨f,a⟩,k⟩
  by_cases hd : P.Boundary (a,k)
  · obtain ⟨⟨i,j⟩,he⟩ := S.complete _ hd
    have hd' : ((f,a),k) = ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) := by rw [he]
    rw [hd',mate_boundary]
    intro h
    have hface := congrArg (fun d : (F×A)×Fin 3 => d.1.1) h
    have hdart := congrArg (fun d : (F×A)×Fin 3 => (d.1.2,d.2)) h
    dsimp only at hdart hface
    have hi := congrArg Prod.fst (S.dart_injective hdart)
    exact M.mate_ne (f,i) (Prod.ext hface hi)
  · rw [mate_internal M P S f (a,k) hd]
    intro h
    apply hd
    exact congrArg (fun d : (F×A)×Fin 3 => (d.1.2,d.2)) h

/-- Boundary vertices glued with opposite side parametrizations. -/
def Seam (u v : F × U) : Prop :=
  ∃ f i j, u = (f,S.point (i,j)) ∧
    v = ((M.mate (f,i)).1,S.point ((M.mate (f,i)).2,j.rev))

abbrev Vertex := Quot (Seam M P S)

def vertex (x : F × U) : Vertex M P S := Quot.mk _ x

omit [NeZero K] in
lemma vertex_seam (f : F) (i : Fin 3) (j : Fin (K+1)) :
    vertex M P S (f,S.point (i,j)) =
      vertex M P S ((M.mate (f,i)).1,S.point ((M.mate (f,i)).2,j.rev)) :=
  Quot.sound ⟨f,i,j,rfl,rfl⟩

def tail (d : (F × A) × Fin 3) : Vertex M P S :=
  vertex M P S (d.1.1,P.tail (d.1.2,d.2))

lemma tail_mateFun (d : (F × A) × Fin 3) :
    tail M P S (mateFun M P S d) = tail M P S (d.1,d.2+1) := by
  rcases d with ⟨⟨f,a⟩,k⟩
  by_cases hd : P.Boundary (a,k)
  · obtain ⟨⟨i,j⟩,he⟩ := S.complete _ hd
    have hd' : ((f,a),k) = ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) := by rw [he]
    rw [hd',mate_boundary]
    change vertex M P S ((M.mate (f,i)).1,P.tail (S.dart ((M.mate (f,i)).2,j.rev))) =
      vertex M P S (f,P.tail ((S.dart (i,j)).1,(S.dart (i,j)).2+1))
    rw [S.tail,S.head,vertex_seam M P S f i j.succ,Fin.rev_succ]
  · rw [mate_internal M P S f (a,k) hd]
    change vertex M P S (f,P.tail (P.mate (a,k))) = vertex M P S (f,P.tail (a,k+1))
    rw [P.tail_mate _ hd]

noncomputable def mesh : TriangleMesh (F × A) (Vertex M P S) where
  mate := ⟨mateFun M P S,mateFun M P S,mateFun_involutive M P S,mateFun_involutive M P S⟩
  mate_involutive := mateFun_involutive M P S
  mate_ne := mateFun_ne M P S
  tail := tail M P S
  tail_mate := tail_mateFun M P S

/-- Substituting an exact triangular patch in every coarse face preserves
exactness. This is a cochain proof, independent of any triangulation theorem. -/
theorem exact (hM : M.Exact) (hP : P.Exact) : (mesh M P S).Exact := by
  classical
  intro w ha hc
  have hf (f : F) : ∃ p : U → ℝ, ∀ d : A × Fin 3,
      w ((f,d.1),d.2) = p (P.tail (d.1,d.2+1)) - p (P.tail d) := by
    apply hP
    · intro d hd
      have h := ha ((f,d.1),d.2)
      change w (mateFun M P S ((f,d.1),d.2)) = -w ((f,d.1),d.2) at h
      rwa [mate_internal M P S f d hd] at h
    · intro a
      exact hc (f,a)
  choose p hp using hf
  let b (f : F) (i : Fin 3) (j : Fin (K+1)) := p f (S.point (i,j))
  have hb (f : F) (i : Fin 3) (j : Fin K) :
      w ((f,(S.dart (i,j)).1),(S.dart (i,j)).2) = b f i j.succ - b f i j.castSucc := by
    simpa only [b,S.head,S.tail] using hp f (S.dart (i,j))
  have hpair (f : F) (i : Fin 3) (j : Fin (K+1)) :
      b f i j - b f i 0 = b (M.mate (f,i)).1 (M.mate (f,i)).2 j.rev -
        b (M.mate (f,i)).1 (M.mate (f,i)).2 (Fin.last K) := by
    apply reverse_chain_difference
    intro j
    have h := ha ((f,(S.dart (i,j)).1),(S.dart (i,j)).2)
    change w (mateFun M P S _) = -w _ at h
    rw [mate_boundary,hb,hb] at h
    linarith
  let W (d : F × Fin 3) := b d.1 d.2 (Fin.last K) - b d.1 d.2 0
  have hWa (d : F × Fin 3) : W (M.mate d) = -W d := by
    have h := hpair d.1 d.2 (Fin.last K)
    simp only [Fin.rev_last] at h
    dsimp only [W]
    linarith
  have hWc (f : F) : ∑ i : Fin 3, W (f,i) = 0 := by
    simp only [W,b,S.ends,Fin.sum_univ_three]
    change (p f (S.point (1,0)) - p f (S.point (0,0))) +
      (p f (S.point (2,0)) - p f (S.point (1,0))) +
      (p f (S.point (0,0)) - p f (S.point (2,0))) = 0
    ring
  obtain ⟨q,hq⟩ := hM W hWa hWc
  have hcorner (f : F) (i : Fin 3) :
      b f i 0 - b f 0 0 = q (M.tail (f,i)) - q (M.tail (f,0)) := by
    have h₀ := hq (f,0)
    have h₁ := hq (f,1)
    simp only [W,b,S.ends] at h₀ h₁
    change p f (S.point (1,0)) - p f (S.point (0,0)) =
      q (M.tail (f,1)) - q (M.tail (f,0)) at h₀
    change p f (S.point (2,0)) - p f (S.point (1,0)) =
      q (M.tail (f,2)) - q (M.tail (f,1)) at h₁
    fin_cases i
    · simp [b]
    · exact h₀
    · change p f (S.point (2,0)) - p f (S.point (0,0)) =
        q (M.tail (f,2)) - q (M.tail (f,0))
      linarith
  let z (v : F × U) := p v.1 v.2 - b v.1 0 0 + q (M.tail (v.1,0))
  have hz {u v : F × U} (h : Seam M P S u v) : z u = z v := by
    obtain ⟨f,i,j,rfl,rfl⟩ := h
    have h₁ := hpair f i j
    have h₂ := hcorner f i
    have h₃ := hcorner (M.mate (f,i)).1 (M.mate (f,i)).2
    have h₄ := hq (M.mate (f,i))
    rw [M.tail_rotate_mate] at h₄
    dsimp only [W] at h₄
    change (b f i j - b f 0 0 + q (M.tail (f,0))) =
      b (M.mate (f,i)).1 (M.mate (f,i)).2 j.rev - b (M.mate (f,i)).1 0 0 +
        q (M.tail ((M.mate (f,i)).1,0))
    linarith
  refine ⟨Quot.lift z (fun _ _ h => hz h),?_⟩
  rintro ⟨⟨f,a⟩,k⟩
  change w ((f,a),k) = z (f,P.tail (a,k+1)) - z (f,P.tail (a,k))
  dsimp only [z]
  rw [hp f (a,k)]
  ring

end Replacement
end TriangleMesh
end ArtinCAT0

namespace ArtinCAT0.GridDisk
variable (H N : ℕ) [NeZero N]

lemma boundary_iff (d : Face H N × Fin 3) :
    (patch H N).Boundary d ↔ ∃ i, d = (A H N (Fin.last H) i,0) := by
  change mateFun H N d = d ↔ _
  rcases d with ⟨f,k⟩
  rcases f with ⟨r,i,b⟩ | i
  · cases b
    · fin_cases k
      · change (if h : r.val+1 < H+1 then (B H N ⟨r.val+1,h⟩ i,1)
          else (A H N r i,0)) = (A H N r i,0) ↔ _
        split_ifs with h
        · have hr : r ≠ Fin.last H := by
            intro he
            have := congrArg Fin.val he
            change r.val = H at this
            omega
          simp [A,B,hr]
        · have hr : r = Fin.last H := by
            apply Fin.ext
            change r.val = H
            have := r.isLt
            omega
          subst r
          simp
      · norm_num [mateFun,A,B]
      · norm_num [mateFun,A,B]
    · fin_cases k
      · norm_num [mateFun,A,B]
      · change (if h : r.val = 0 then (C H N i,0)
          else (A H N ⟨r.val-1,by omega⟩ i,0)) = (B H N r i,1) ↔ _
        split_ifs <;> simp [A,B,C]
      · norm_num [mateFun,A,B]
  · fin_cases k <;> norm_num [mateFun,A,B,C] <;> simp

variable (K : ℕ) [NeZero K]

def sideIndex (i : Fin 3) (j : Fin (K+1)) : Fin (3*K) :=
  ⟨(i.val*K+j.val) % (3*K),Nat.mod_lt _ (Nat.mul_pos (by decide) (NeZero.pos K))⟩

def sideDart (e : Fin 3 × Fin K) : Face H (3*K) × Fin 3 :=
  (A H (3*K) (Fin.last H) (finProdFinEquiv e),0)

def sidePoint (e : Fin 3 × Fin (K+1)) : Vertex H (3*K) :=
  Sum.inl (Fin.last (H+1),sideIndex K e.1 e.2)

lemma sideIndex_castSucc (i : Fin 3) (j : Fin K) :
    sideIndex K i j.castSucc = finProdFinEquiv (i,j) := by
  apply Fin.ext
  change (i.val*K+j.val) % (3*K) = j.val + K*i.val
  rw [Nat.mul_comm i.val K, Nat.add_comm]
  exact Nat.mod_eq_of_lt (finProdFinEquiv (i,j)).isLt

lemma sideIndex_succ (i : Fin 3) (j : Fin K) :
    sideIndex K i j.succ = finProdFinEquiv (i,j) + 1 := by
  apply Fin.ext
  change (i.val*K+(j.val+1)) % (3*K) = ((j.val+K*i.val)+(1 % (3*K))) % (3*K)
  rw [Nat.mod_eq_of_lt (show 1 < 3*K by have := NeZero.pos K; omega)]
  congr 1
  ring

lemma sidePoint_ends (i : Fin 3) :
    sidePoint H K (i,Fin.last K) = sidePoint H K (i+1,0) := by
  apply congrArg Sum.inl
  congr 1
  apply Fin.ext
  fin_cases i
  · change (0*K+K) % (3*K) = (1*K+0) % (3*K)
    simp
  · change (1*K+K) % (3*K) = (2*K+0) % (3*K)
    congr 1; ring
  · change (2*K+K) % (3*K) = (0*K+0) % (3*K)
    rw [show 2*K+K = 3*K by omega]
    simp

noncomputable def sides : (patch H (3*K)).Sides K where
  dart := sideDart H K
  point := sidePoint H K
  dart_injective := by
    intro e e' h
    apply finProdFinEquiv.injective
    simpa only [sideDart,A,Prod.mk.injEq,Sum.inl.injEq,true_and,and_true] using h
  fixed := by
    intro ⟨i,j⟩
    exact (boundary_iff H (3*K) _).2 ⟨_,rfl⟩
  complete := by
    intro d hd
    obtain ⟨i,rfl⟩ := (boundary_iff H (3*K) d).1 hd
    refine ⟨finProdFinEquiv.symm i,?_⟩
    change (A H (3*K) (Fin.last H) (finProdFinEquiv (finProdFinEquiv.symm i)),0) = _
    rw [Equiv.apply_symm_apply]
  tail := by
    intro i j
    change Sum.inl ((Fin.last H).succ,finProdFinEquiv (i,j)) =
      Sum.inl (Fin.last (H+1),sideIndex K i j.castSucc)
    rw [sideIndex_castSucc]
    rfl
  head := by
    intro i j
    change Sum.inl ((Fin.last H).succ,finProdFinEquiv (i,j)+1) =
      Sum.inl (Fin.last (H+1),sideIndex K i j.succ)
    rw [sideIndex_succ]
    rfl
  ends := sidePoint_ends H K

end ArtinCAT0.GridDisk

namespace ArtinCAT0.TriangleMesh

/-- The sphere consisting of two oppositely oriented triangles. -/
def doubleTriangle : TriangleMesh Bool (Fin 3) where
  mate := (show Function.Involutive (fun d : Bool × Fin 3 => (!d.1,-d.2-1)) from
    fun d => by rcases d with ⟨b,i⟩; simp).toPerm
  mate_involutive := by rintro ⟨b,i⟩; simp
  mate_ne := by rintro ⟨b,i⟩ h; have := congrArg Prod.fst h; cases b <;> simp at this
  tail := fun d => if d.1 then -d.2 else d.2
  tail_mate := by rintro ⟨b,i⟩; cases b <;> simp <;> abel

lemma doubleTriangle_exact : doubleTriangle.Exact := by
  intro w hw hf
  let p : Fin 3 → ℝ := fun i => if i = 0 then 0 else if i = 1 then w (false,0)
    else w (false,0)+w (false,1)
  have hs : w (false,0)+w (false,1)+w (false,2) = 0 := by
    simpa only [Fin.sum_univ_three,add_assoc] using hf false
  have he (i : Fin 3) : w (false,i) = p (i+1)-p i := by
    fin_cases i
    · change w (false,0) = p 1-p 0
      simp [p]
    · change w (false,1) = p 2-p 1
      simp [p,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide]
    · change w (false,2) = p 0-p 2
      simp [p,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide]
      linarith
  refine ⟨p,?_⟩
  rintro ⟨b,i⟩
  cases b
  · exact he i
  · have hm := hw (false,-i-1)
    change w (true,-(-i-1)-1) = -w (false,-i-1) at hm
    rw [show -(-i-1)-1 = i by abel,he] at hm
    change w (true,i) = p (-(i+1))-p (-i)
    rw [hm,show -i-1+1 = -i by abel,show -i-1 = -(i+1) by abel]
    ring

end ArtinCAT0.TriangleMesh

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0.WordDiagram

abbrev Letter := Fin 3 × Bool
abbrev Word := FreeMonoid Letter

def positive (i : Fin 3) : Word := FreeMonoid.of (i,true)
def signed (s : Letter) : TriangleGroup := if s.2 then triangleGen s.1 else (triangleGen s.1)⁻¹

inductive Rel : Word → Word → Prop
  | cancel (s : Letter) : Rel (FreeMonoid.of s * FreeMonoid.of (s.1,!s.2)) 1
  | braid (i : Fin 3) : Rel (positive i * positive (i+1) * positive i)
      (positive (i+1) * positive i * positive (i+1))

abbrev P := PresentedMonoid Rel

def eval : Word →* TriangleGroup := FreeMonoid.lift signed

lemma rel_sound {u v : Word} (h : Rel u v) : eval u = eval v := by
  cases h with
  | cancel s => rcases s with ⟨i,b⟩; cases b <;> simp [eval,signed]
  | braid i => simpa [eval,positive,signed] using triangle_braid i

lemma isUnit_of (s : Letter) : IsUnit (PresentedMonoid.of Rel s) := by
  let a := PresentedMonoid.of Rel s
  let b := PresentedMonoid.of Rel (s.1,!s.2)
  have hab : a*b = 1 := by
    simpa only [a,b,PresentedMonoid.of,map_mul,map_one] using
      PresentedMonoid.mk_eq_mk_of_rel (Rel.cancel s)
  have hba : b*a = 1 := by
    simpa only [a,b,PresentedMonoid.of,map_mul,map_one,Bool.not_not] using
      PresentedMonoid.mk_eq_mk_of_rel (Rel.cancel (s.1,!s.2))
  exact ⟨⟨a,b,hab,hba⟩,rfl⟩

lemma all_isUnit (x : P) : IsUnit x := by
  induction x using PresentedMonoid.inductionOn with | h w =>
    induction w with
    | one => exact isUnit_one
    | of s => exact isUnit_of s
    | mul a b ha hb => exact ha.mul hb

noncomputable instance : Group P := groupOfIsUnit all_isUnit

lemma negative_of (i : Fin 3) :
    PresentedMonoid.of Rel (i,false) = (PresentedMonoid.of Rel (i,true))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simpa only [PresentedMonoid.of,map_mul,map_one,Bool.not_true] using
    PresentedMonoid.mk_eq_mk_of_rel (Rel.cancel (i,true))

noncomputable def fromTriangle : TriangleGroup →* P :=
  triangleLift (fun i => PresentedMonoid.of Rel (i,true)) (by
    intro i
    simpa only [positive,PresentedMonoid.of,map_mul] using
      PresentedMonoid.mk_eq_mk_of_rel (Rel.braid i))

lemma fromTriangle_eval : fromTriangle.comp eval = PresentedMonoid.mk Rel := by
  apply FreeMonoid.hom_eq
  rintro ⟨i,b⟩
  cases b
  · simpa [eval,signed,fromTriangle,triangleLift_gen,PresentedMonoid.of] using (negative_of i).symm
  · simp [eval,signed,fromTriangle,triangleLift_gen,PresentedMonoid.of]

/-- Null words have actual finite derivations from cancellation and braid moves;
this is not an assumed van Kampen theorem. -/
theorem null_derivation (w : Word) (h : eval w = 1) : conGen Rel w 1 := by
  apply PresentedMonoid.mk_eq_mk_iff.1
  rw [← fromTriangle_eval]
  simp [h]

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation

/-- A single local cancellation or braid replacement, with fixed contexts. -/
inductive Step : Word → Word → Prop
  | context (l r : Word) {u v : Word} (h : Rel u v) : Step (l*u*r) (l*v*r)

lemma step_context {u v : Word} (h : Step u v) (l r : Word) : Step (l*u*r) (l*v*r) := by
  cases h with
  | context a b h => simpa only [mul_assoc] using Step.context (l*a) (b*r) h

lemma homotopy_context {u v : Word} (h : EqvGen Step u v) (l r : Word) :
    EqvGen Step (l*u*r) (l*v*r) := by
  induction h with
  | rel a b h => exact .rel _ _ (step_context h l r)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih1 ih2 => exact .trans _ _ _ ih1 ih2

lemma derivation_homotopy {u v : Word} (h : conGen Rel u v) : EqvGen Step u v := by
  induction h with
  | of u v h =>
    simpa only [one_mul,mul_one] using EqvGen.rel _ _ (Step.context 1 1 h)
  | refl u => exact .refl _
  | symm h ih => exact .symm _ _ ih
  | trans h1 h2 ih1 ih2 => exact .trans _ _ _ ih1 ih2
  | @mul w x y z h1 h2 ih1 ih2 =>
    exact .trans _ _ _ (by simpa only [one_mul] using homotopy_context ih1 1 y)
      (by simpa only [mul_one] using homotopy_context ih2 x 1)

theorem null_local_moves (w : Word) (h : eval w = 1) :
    ReflTransGen (SymmGen Step) w 1 := by
  rw [EqvGen.reflTransGen_symmGen]
  exact derivation_homotopy (null_derivation w h)

end ArtinCAT0.WordDiagram

namespace ArtinCAT0

def positiveValue (q : Fin 9) : TriangleGroup :=
  if h : q.val < 3 then triangleGen ⟨q.val,h⟩
  else if h' : q.val < 6 then triangleX ⟨q.val-3,by omega⟩ 2
  else triangleH ⟨q.val-6,by omega⟩

def positivePerm (q : Fin 9) : Equiv.Perm Mirror :=
  if h : q.val < 3 then mirrorPerm ⟨q.val,h⟩
  else if h' : q.val < 6 then
    let b : Fin 3 := ⟨q.val-3,by omega⟩
    (mirrorPerm (b+1))⁻¹ * mirrorPerm b * mirrorPerm (b+1)
  else
    let b : Fin 3 := ⟨q.val-6,by omega⟩
    mirrorPerm b * mirrorPerm (b+1)

def positiveDegree (q : Fin 9) : ℤ := if q.val < 6 then 1 else 2

def directionValue (d : LinkDirection) : TriangleGroup :=
  if h : d.val < 9 then positiveValue ⟨d.val,h⟩
  else (positiveValue ⟨d.val-9,by omega⟩)⁻¹

def directionPerm (d : LinkDirection) : Equiv.Perm Mirror :=
  if h : d.val < 9 then positivePerm ⟨d.val,h⟩
  else (positivePerm ⟨d.val-9,by omega⟩)⁻¹

def directionDegree (d : LinkDirection) : ℤ :=
  if h : d.val < 9 then positiveDegree ⟨d.val,h⟩
  else -positiveDegree ⟨d.val-9,by omega⟩

@[simp] lemma positiveValue_xLetter (b i : Fin 3) : positiveValue (xLetter b i) = triangleX b i := by
  fin_cases b <;> fin_cases i <;> rfl

@[simp] lemma positiveValue_hLetter (b : Fin 3) : positiveValue (hLetter b) = triangleH b := by
  fin_cases b <;> rfl

@[simp] lemma directionValue_positive (q : Fin 9) : directionValue (positiveDirection q) = positiveValue q := by
  simp [directionValue,positiveDirection,q.isLt]

@[simp] lemma directionValue_negative (q : Fin 9) : directionValue (negativeDirection q) = (positiveValue q)⁻¹ := by
  simp [directionValue,negativeDirection,show ¬q.val+9 < 9 by omega]

lemma positiveValue_linear (q : Fin 9) : mirrorLinear (positiveValue q) = positivePerm q := by
  fin_cases q <;> simp [positiveValue,positivePerm,mirrorLinear,triangleX,triangleH,mirrorGenerator]

lemma positiveValue_degree (q : Fin 9) :
    (triangleExponent (positiveValue q)).toAdd = positiveDegree q := by
  fin_cases q <;> norm_num [positiveValue,positiveDegree]

lemma directionValue_linear (d : LinkDirection) :
    mirrorLinear (directionValue d) = directionPerm d := by
  unfold directionValue directionPerm
  split_ifs
  · exact positiveValue_linear _
  · simp only [mirrorLinear,map_inv,SemidirectProduct.inv_right]
    exact congrArg Inv.inv (positiveValue_linear _)

lemma directionValue_degree (d : LinkDirection) :
    (triangleExponent (directionValue d)).toAdd = directionDegree d := by
  unfold directionValue directionDegree
  split_ifs
  · exact positiveValue_degree _
  · simpa using congrArg Neg.neg (positiveValue_degree ⟨d.val-9,by omega⟩)

def directionSignature (d : LinkDirection) : ℤ × Mirror × Mirror × Mirror :=
  (directionDegree d,directionPerm d (0,0),directionPerm d (1,0),directionPerm d (2,0))

lemma directionSignature_injective : Function.Injective directionSignature := by decide

lemma directionValue_injective : Function.Injective directionValue := by
  intro d e h
  apply directionSignature_injective
  unfold directionSignature
  have hp := congrArg mirrorLinear h
  rw [directionValue_linear,directionValue_linear] at hp
  have hd := congrArg (fun x => (triangleExponent x).toAdd) h
  rw [directionValue_degree,directionValue_degree] at hd
  rw [hp,hd]

lemma TargetTriangle.difference (c : TargetTriangle) (s t : Fin 3) (h : s ≠ t) :
    (c.vertex s)⁻¹ * c.vertex t = directionValue (c.direction s t) := by
  have hr := triangular_relation c.block c.rel
  unfold TargetTriangle.direction
  fin_cases s <;> fin_cases t <;> try contradiction
  all_goals simp [TargetTriangle.vertex,cellDirection,Fin.ext_iff]
  all_goals rw [← hr]
  all_goals group

end ArtinCAT0

namespace ArtinCAT0.TriangleMesh

variable {F V : Type*} (M : TriangleMesh F V)

/-- Group-vertex labels determine the labelled directions: the nine positive
letters and their inverses are distinct in the actual triangle Artin group. -/
noncomputable def SimplicialLabeling.ofVertices (v : V → TriangleGroup)
    (h : ∀ f : F, ∃ c : TargetTriangle, ∀ i : Fin 3, ∃ j, c.vertex j = v (M.tail (f,i))) :
    M.SimplicialLabeling := by
  classical
  choose c k hk using h
  have hv (f : F) (i : Fin 3) : v (M.tail (f,i)) = (c f).vertex (k f i) := (hk f i).symm
  have he (f : F) (i j : Fin 3) :
      k f i ≠ k f j ↔ v (M.tail (f,i)) ≠ v (M.tail (f,j)) := by
    rw [hv,hv]
    exact not_congr (c f).vertex_injective.eq_iff.symm
  refine ⟨c,k,v,fun d => hv d.1 d.2,?_,?_⟩
  · intro d
    rw [he,he]
    change v (M.tail (M.mate d)) ≠ v (M.tail (rotate (M.mate d))) ↔ _
    rw [M.tail_mate,M.tail_rotate_mate]
    exact ne_comm
  · intro d hd
    have hm : k (M.mate d).1 (M.mate d).2 ≠ k (M.mate d).1 ((M.mate d).2+1) := by
      rw [he]
      change v (M.tail (M.mate d)) ≠ v (M.tail (rotate (M.mate d)))
      rw [M.tail_mate,M.tail_rotate_mate]
      exact ((he d.1 d.2 (d.2+1)).1 hd).symm
    change (c (M.mate d).1).direction _ _ = reverseDirection ((c d.1).direction _ _)
    rw [show reverseDirection ((c d.1).direction (k d.1 d.2) (k d.1 (d.2+1))) =
      (c d.1).direction (k d.1 (d.2+1)) (k d.1 d.2) from
      (cellDirection_reverse _ _ _ _ hd).symm]
    apply directionValue_injective
    rw [← TargetTriangle.difference _ _ _ hm,← TargetTriangle.difference _ _ _ hd.symm]
    rw [← hv,← hv,← hv,← hv]
    change (v (M.tail (M.mate d)))⁻¹ * v (M.tail (rotate (M.mate d))) = _
    rw [M.tail_mate,M.tail_rotate_mate]

end ArtinCAT0.TriangleMesh

namespace ArtinCAT0.WordDiagram
open Relation

def Legal (a b c : TriangleGroup) : Prop :=
  ∃ t : TargetTriangle, ∃ i j k : Fin 3, t.vertex i = a ∧ t.vertex j = b ∧ t.vertex k = c

lemma Legal.of_corners (t : TargetTriangle) (i j k : Fin 3) :
    Legal (t.vertex i) (t.vertex j) (t.vertex k) := ⟨t,i,j,k,rfl,rfl,rfl⟩

lemma Legal.constant (g : TriangleGroup) : Legal g g g := by
  refine ⟨⟨g,0,0⟩,0,0,0,?_,?_,?_⟩ <;> simp [TargetTriangle.vertex]

lemma Legal.swap (a b c : TriangleGroup) (h : Legal a b c) : Legal c b a := by
  obtain ⟨t,i,j,k,h1,h2,h3⟩ := h
  exact ⟨t,k,j,i,h3,h2,h1⟩

lemma legal_signed (g : TriangleGroup) (s : Letter) : Legal g (g*signed s) g := by
  rcases s with ⟨i,b⟩
  cases b
  · refine ⟨⟨g*(triangleGen i)⁻¹,i,0⟩,1,0,1,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,signed]
  · refine ⟨⟨g,i,0⟩,0,1,0,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,signed]

inductive PathStep : List TriangleGroup → List TriangleGroup → Prop
  | triangle (l r : List TriangleGroup) {a b c : TriangleGroup} (h : Legal a b c) :
      PathStep (l ++ [a,b,c] ++ r) (l ++ [a,c] ++ r)
  | stutter (l r : List TriangleGroup) (a : TriangleGroup) :
      PathStep (l ++ [a,a] ++ r) (l ++ [a] ++ r)

abbrev PathHomotopy := EqvGen PathStep

lemma pathStep_context {u v : List TriangleGroup} (h : PathStep u v) (l r : List TriangleGroup) :
    PathStep (l++u++r) (l++v++r) := by
  cases h with
  | triangle a b h => simpa only [List.append_assoc] using PathStep.triangle (l++a) (b++r) h
  | stutter a b g => simpa only [List.append_assoc] using PathStep.stutter (l++a) (b++r) g

lemma path_context {u v : List TriangleGroup} (h : PathHomotopy u v) (l r : List TriangleGroup) :
    PathHomotopy (l++u++r) (l++v++r) := by
  induction h with
  | rel a b h => exact .rel _ _ (pathStep_context h l r)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih1 ih2 => exact .trans _ _ _ ih1 ih2

def walk (g : TriangleGroup) : List Letter → List TriangleGroup
  | [] => [g]
  | s::w => g :: walk (g*signed s) w

lemma walk_ne_nil (g : TriangleGroup) (w : List Letter) : walk g w ≠ [] := by cases w <;> simp [walk]
lemma walk_head (g : TriangleGroup) (w : List Letter) : (walk g w).head (walk_ne_nil g w) = g := by
  cases w <;> rfl

lemma eval_cons (s : Letter) (w : List Letter) :
    eval (FreeMonoid.ofList (s::w)) = signed s * eval (FreeMonoid.ofList w) := by
  simp [eval]

lemma walk_append (g : TriangleGroup) (u v : List Letter) :
    walk g (u++v) = (walk g u).dropLast ++ walk (g*eval (FreeMonoid.ofList u)) v := by
  induction u generalizing g with
  | nil => simp [walk]
  | cons s u ih =>
    simp only [walk, List.dropLast_cons_of_ne_nil (walk_ne_nil _ _), List.cons_append, ih]
    simp [eval,mul_assoc]

lemma walk_concat (g : TriangleGroup) (u v : List Letter) :
    PathHomotopy (walk g (u++v)) (walk g u ++ walk (g*eval (FreeMonoid.ofList u)) v) := by
  induction u generalizing g with
  | nil =>
    cases v with
    | nil => simpa [walk] using EqvGen.symm _ _ (EqvGen.rel _ _ (PathStep.stutter [] [] g))
    | cons s v =>
      simpa [walk] using EqvGen.symm _ _ (EqvGen.rel _ _ (PathStep.stutter [] (walk (g*signed s) v) g))
  | cons s u ih =>
    simpa [walk,eval,mul_assoc] using path_context (ih (g*signed s)) [g] []

lemma braid_path (g : TriangleGroup) (i : Fin 3) :
    PathHomotopy
      [g,g*triangleGen i,g*triangleGen i*triangleGen (i+1),g*triangleGen i*triangleGen (i+1)*triangleGen i]
      [g,g*triangleGen (i+1),g*triangleGen (i+1)*triangleGen i,g*triangleGen (i+1)*triangleGen i*triangleGen (i+1)] := by
  let u := triangleGen i
  let v := triangleGen (i+1)
  have hb : g*u*v*u = g*v*u*v := by simpa [u,v,mul_assoc] using congrArg (g*·) (triangle_braid i)
  have h1 : Legal g (g*u) (g*u*v) := by
    refine ⟨⟨g,i,0⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  have h2 : Legal g (g*v) (g*u*v) := by
    refine ⟨⟨g,i,1⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  have h3 : Legal (g*v) (g*u*v) (g*v*u*v) := by
    refine ⟨⟨g*v,i,2⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  have h4 : Legal (g*v) (g*v*u) (g*v*u*v) := by
    refine ⟨⟨g*v,i,0⟩,0,1,2,?_,?_,?_⟩
    all_goals simp [TargetTriangle.vertex,triangleX,triangleH,u,v,mul_assoc,Fin.ext_iff]
  change PathHomotopy [g,g*u,g*u*v,g*u*v*u] [g,g*v,g*v*u,g*v*u*v]
  rw [hb]
  exact .trans _ _ _ (.rel _ _ (PathStep.triangle [] [g*v*u*v] h1))
    (.trans _ _ _ (.symm _ _ (.rel _ _ (PathStep.triangle [] [g*v*u*v] h2)))
      (.trans _ _ _ (.rel _ _ (PathStep.triangle [g] [] h3))
        (.symm _ _ (.rel _ _ (PathStep.triangle [g] [] h4)))))

lemma rel_path (g : TriangleGroup) {u v : Word} (h : Rel u v) :
    PathHomotopy (walk g u.toList) (walk g v.toList) := by
  cases h with
  | cancel s =>
    have hi : signed s * signed (s.1,!s.2) = 1 := by
      rcases s with ⟨i,b⟩; cases b <;> simp [signed]
    change PathHomotopy [g,g*signed s,g*signed s*signed (s.1,!s.2)] [g]
    rw [mul_assoc,hi,mul_one]
    exact .trans _ _ _ (.rel _ _ (PathStep.triangle [] [] (legal_signed g s)))
      (.rel _ _ (PathStep.stutter [] [] g))
  | braid i => simpa [walk,positive,signed,mul_assoc] using braid_path g i

lemma step_sound {u v : Word} (h : Step u v) : eval u = eval v := by
  cases h with
  | context l r h => simp only [map_mul,rel_sound h]

lemma walk_context {u v : Word} (he : eval u = eval v)
    (h : ∀ g, PathHomotopy (walk g u.toList) (walk g v.toList))
    (l r : Word) (g : TriangleGroup) :
    PathHomotopy (walk g (l*u*r).toList) (walk g (l*v*r).toList) := by
  have splitwalk (w : Word) : PathHomotopy (walk g (l*w*r).toList)
      (walk g l.toList ++ walk (g*eval l) w.toList ++ walk (g*eval l*eval w) r.toList) := by
    exact .trans _ _ _ (walk_concat g (l*w).toList r.toList)
      (by simpa [mul_assoc] using (path_context (walk_concat g l.toList w.toList) []
        (walk (g*eval l*eval w) r.toList)))
  exact .trans _ _ _ (splitwalk u) (.trans _ _ _
    (by simpa only [List.append_assoc,he] using
      path_context (h (g*eval l)) (walk g l.toList) (walk (g*eval l*eval u) r.toList))
    (.symm _ _ (splitwalk v)))

lemma step_path {u v : Word} (h : Step u v) (g : TriangleGroup) :
    PathHomotopy (walk g u.toList) (walk g v.toList) := by
  cases h with
  | context l r h => exact walk_context (rel_sound h) (fun g => rel_path g h) l r g

lemma homotopy_path {u v : Word} (h : EqvGen Step u v) (g : TriangleGroup) :
    PathHomotopy (walk g u.toList) (walk g v.toList) := by
  induction h with
  | rel a b h => exact step_path h g
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h1 h2 ih1 ih2 => exact .trans _ _ _ ih1 ih2

/-- Every null word admits an explicit finite homotopy using only actual
triangles of the Cayley complex and repeated vertices. -/
theorem null_path (w : Word) (hw : eval w = 1) (g : TriangleGroup) :
    PathHomotopy (walk g w.toList) [g] :=
  homotopy_path (derivation_homotopy (null_derivation w hw)) g

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation Fin.NatCast

lemma Legal.permute {a b c : TriangleGroup} (h : Legal a b c) :
    Legal b c a ∧ Legal a c b ∧ Legal a b a ∧ Legal b c b ∧ Legal a c a := by
  obtain ⟨t,i,j,k,hi,hj,hk⟩ := h
  exact ⟨⟨t,j,k,i,hj,hk,hi⟩,⟨t,i,k,j,hi,hk,hj⟩,⟨t,i,j,i,hi,hj,hi⟩,
    ⟨t,j,k,j,hj,hk,hj⟩,⟨t,i,k,i,hi,hk,hi⟩⟩

abbrev Edge (a b : TriangleGroup) := Legal a b a
lemma edge_refl (a : TriangleGroup) : Edge a a := Legal.constant a
lemma edge_symm {a b : TriangleGroup} (h : Edge a b) : Edge b a := by
  obtain ⟨t,i,j,k,hi,hj,_⟩ := h
  exact ⟨t,j,i,j,hj,hi,hj⟩
lemma edge_dup {a b : TriangleGroup} (h : Edge a b) : Legal a b b := by
  obtain ⟨t,i,j,k,hi,hj,_⟩ := h
  exact ⟨t,i,j,j,hi,hj,hj⟩

variable {N : ℕ} [NeZero N]
abbrev Row (N : ℕ) := Fin N → TriangleGroup

def RowGood (x : Row N) : Prop := ∀ i, Edge (x i) (x (i+1))
def Strip (x y : Row N) : Prop := ∀ i,
  Legal (y i) (y (i+1)) (x (i+1)) ∧ Legal (y i) (x (i+1)) (x i)

lemma strip_good {x y : Row N} (h : Strip x y) : RowGood x ∧ RowGood y := by
  constructor <;> intro i
  · exact edge_symm (h i).2.permute.2.2.2.1
  · exact (h i).1.permute.2.2.1

lemma strip_refl {x : Row N} (h : RowGood x) : Strip x x := by
  intro i
  exact ⟨edge_dup (h i), h i⟩

lemma strip_rotate (x : Row N) (h : RowGood x) : Strip x (fun i => x (i+1)) := by
  intro i
  exact ⟨h (i+1), Legal.swap _ _ _ (edge_dup (h i))⟩

lemma strip_swap_rotate {x y : Row N} (h : Strip x y) : Strip y (fun i => x (i+1)) := by
  intro i
  exact ⟨Legal.swap _ _ _ (h (i+1)).2, Legal.swap _ _ _ (h i).1⟩

lemma good_shift {x : Row N} (h : RowGood x) (k : Fin N) : RowGood (fun i => x (i+k)) := by
  intro i
  simpa only [add_right_comm] using h (i+k)

lemma reachable_rotate (x : Row N) (h : RowGood x) (k : ℕ) :
    ReflTransGen Strip x (fun i => x (i+(k : Fin N))) := by
  induction k with
  | zero => simpa using (ReflTransGen.refl : ReflTransGen Strip x x)
  | succ k ih =>
    apply ih.tail
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      strip_rotate (fun i => x (i+(k : Fin N))) (good_shift h _)

lemma strip_symmetric {x y : Row N} (h : Strip x y) : ReflTransGen Strip y x := by
  have hn : 0 < N := NeZero.pos N
  have hrot := reachable_rotate (fun i => x (i+1)) (good_shift (strip_good h).1 1) (N-1)
  have eq : (fun i : Fin N => x (i+(N-1 : ℕ)+1)) = x := by
    funext i
    congr 1
    have hc : ((N-1 : ℕ) : Fin N) + 1 = 0 := by
      calc
        _ = ((N-1+1 : ℕ) : Fin N) := by rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := by rw [Nat.sub_add_cancel hn,Fin.natCast_self]
    simp only [add_assoc,hc,add_zero]
  refine (ReflTransGen.single (strip_swap_rotate h)).trans ?_
  simpa only [eq] using hrot

lemma strip_reach_reverse {x y : Row N} (h : ReflTransGen Strip x y) : ReflTransGen Strip y x := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih => exact (strip_symmetric h2).trans ih

lemma strip_homotopy {x y : Row N} (h : EqvGen Strip x y) : ReflTransGen Strip x y := by
  induction h with
  | rel a b h => exact .single h
  | refl a => exact .refl
  | symm a b h ih => exact strip_reach_reverse ih
  | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation Fin.NatCast

lemma getD_append_formula (l r : List TriangleGroup) (g : TriangleGroup) (n : ℕ) :
    (l++r).getD n g = if n < l.length then l.getD n g else r.getD (n-l.length) g := by
  simp only [List.getD, List.getElem?_append]
  split_ifs <;> rfl

lemma getD_delete (l r : List TriangleGroup) (a b g : TriangleGroup) (n : ℕ) :
    (l++a::r).getD n g = if n ≤ l.length then (l++a::b::r).getD n g
      else (l++a::b::r).getD (n+1) g := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.cons_append,List.getD_cons_succ,List.length_cons,Nat.add_le_add_iff_right] using ih n

lemma getD_stutter (l r : List TriangleGroup) (a g : TriangleGroup) (n : ℕ) :
    (l++a::r).getD n g = if n < l.length then (l++a::a::r).getD n g
      else (l++a::a::r).getD (n+1) g := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.cons_append,List.getD_cons_succ,List.length_cons,Nat.add_lt_add_iff_right] using ih n

def GoodPath (g : TriangleGroup) (p : List TriangleGroup) : Prop :=
  p.headD g = g ∧ List.IsChain Edge (p++[g])

lemma step_good {p q : List TriangleGroup} (h : PathStep p q) (g : TriangleGroup) :
    GoodPath g p ↔ GoodPath g q := by
  cases h with
  | @triangle l r a b c h =>
    obtain ⟨hbc,hac,hab,hbc',hac'⟩ := h.permute
    dsimp [GoodPath]
    have heads : (l++[a,b,c]++r).headD g = (l++[a,c]++r).headD g := by
      cases l <;> rfl
    rw [heads]
    simp only [List.append_assoc,List.isChain_append,List.isChain_cons_cons,
      List.head?_cons,List.cons_append,List.nil_append,Option.mem_def,hab,hbc',hac',true_and]
  | stutter l r a =>
    dsimp [GoodPath]
    have heads : (l++[a,a]++r).headD g = (l++[a]++r).headD g := by
      cases l <;> rfl
    rw [heads]
    simp only [List.append_assoc,List.isChain_append,List.isChain_cons_cons,
      List.head?_cons,List.cons_append,List.nil_append,Option.mem_def,edge_refl,true_and]

lemma goodPath_padded {g : TriangleGroup} {p : List TriangleGroup} (h : GoodPath g p) (n : ℕ) :
    Edge (p.getD n g) (p.getD (n+1) g) := by
  by_cases hn : n+1 < p.length
  · have hc := List.isChain_iff_getElem.1 h.2 n (by simp; omega)
    rw [List.getD_eq_getElem _ _ (by omega : n<p.length), List.getD_eq_getElem _ _ hn]
    simpa only [List.getElem_append_left (by omega : n < p.length),
      List.getElem_append_left hn] using hc
  · by_cases hn' : n < p.length
    · have hn'' : n+1 = p.length := by omega
      have hc := List.isChain_iff_getElem.1 h.2 n (by simp; omega)
      rw [List.getD_eq_getElem _ _ hn', List.getD_eq_default _ _ (by omega : p.length≤n+1)]
      simpa [List.getElem_append_left hn',List.getElem_append_right (by omega : p.length ≤ n+1),hn''] using hc
    · rw [List.getD_eq_default _ _ (by omega : p.length≤n),
        List.getD_eq_default _ _ (by omega : p.length≤n+1)]
      exact edge_refl g

variable {N : ℕ} [NeZero N]
def padded (g : TriangleGroup) (p : List TriangleGroup) : Row N := fun i => p.getD i.val g

lemma padded_good {g : TriangleGroup} {p : List TriangleGroup} (h : GoodPath g p)
    (hn : p.length ≤ N) : RowGood (padded g p : Row N) := by
  intro i
  have hiv : (i+1).val = (i.val+1)%N := by simp [Fin.val_add,Nat.add_mod]
  by_cases hi : i.val+1 < N
  · simpa only [padded,hiv,Nat.mod_eq_of_lt hi] using goodPath_padded h i.val
  · have he : i.val+1 = N := by omega
    have he0 : p.getD 0 g = g := by simpa only [← List.headD_eq_getD] using h.1
    simp only [padded,hiv,he,Nat.mod_self,he0]
    simpa only [List.getD_eq_default _ _ (by omega : p.length ≤ i.val+1)] using goodPath_padded h i.val

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation Fin.NatCast

lemma triangle_strip_nat (l r : List TriangleGroup) (a b c g : TriangleGroup)
    (h : Legal a b c)
    (hp : ∀ n, Edge ((l++[a,b,c]++r).getD n g) ((l++[a,b,c]++r).getD (n+1) g)) (n : ℕ) :
    Legal ((l++[a,c]++r).getD n g) ((l++[a,c]++r).getD (n+1) g) ((l++[a,b,c]++r).getD (n+1) g) ∧
    Legal ((l++[a,c]++r).getD n g) ((l++[a,b,c]++r).getD (n+1) g) ((l++[a,b,c]++r).getD n g) := by
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hp ⊢
  by_cases hn : n < l.length
  · rw [getD_delete l (c::r) a b g n, getD_delete l (c::r) a b g (n+1)]
    simp only [ite_eq_left (show n ≤ l.length by omega), ite_eq_left (show n+1 ≤ l.length by omega)]
    exact ⟨edge_dup (hp n), hp n⟩
  · by_cases he : n = l.length
    · subst n
      simpa [getD_append_formula] using And.intro h.permute.2.1 h.permute.2.2.1
    · rw [getD_delete l (c::r) a b g n, getD_delete l (c::r) a b g (n+1)]
      simp only [ite_eq_right (show ¬n ≤ l.length by omega), ite_eq_right (show ¬n+1 ≤ l.length by omega)]
      exact ⟨hp (n+1), Legal.swap _ _ _ (edge_dup (hp n))⟩

lemma stutter_strip_nat (l r : List TriangleGroup) (a g : TriangleGroup)
    (hp : ∀ n, Edge ((l++[a,a]++r).getD n g) ((l++[a,a]++r).getD (n+1) g)) (n : ℕ) :
    Legal ((l++[a]++r).getD n g) ((l++[a]++r).getD (n+1) g) ((l++[a,a]++r).getD (n+1) g) ∧
    Legal ((l++[a]++r).getD n g) ((l++[a,a]++r).getD (n+1) g) ((l++[a,a]++r).getD n g) := by
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hp ⊢
  by_cases hn : n < l.length
  · rw [getD_delete l r a a g n, getD_delete l r a a g (n+1)]
    simp only [ite_eq_left (show n ≤ l.length by omega), ite_eq_left (show n+1 ≤ l.length by omega)]
    exact ⟨edge_dup (hp n), hp n⟩
  · rw [getD_stutter l r a g n, getD_stutter l r a g (n+1)]
    simp only [ite_eq_right hn, ite_eq_right (show ¬n+1 < l.length by omega)]
    exact ⟨hp (n+1), Legal.swap _ _ _ (edge_dup (hp n))⟩

variable {N : ℕ} [NeZero N]
lemma strip_padded_of_nat {g : TriangleGroup} {p q : List TriangleGroup}
    (hp : GoodPath g p) (hq : GoodPath g q) (hnp : p.length ≤ N) (hnq : q.length ≤ N)
    (h : ∀ n, Legal (q.getD n g) (q.getD (n+1) g) (p.getD (n+1) g) ∧
      Legal (q.getD n g) (p.getD (n+1) g) (p.getD n g)) :
    Strip (padded g p : Row N) (padded g q) := by
  intro i
  have hiv : (i+1).val = (i.val+1)%N := by simp [Fin.val_add,Nat.add_mod]
  by_cases hi : i.val+1 < N
  · simpa only [padded,hiv,Nat.mod_eq_of_lt hi] using h i.val
  · have he : i.val+1 = N := by omega
    have hp0 : p.getD 0 g = g := by simpa only [← List.headD_eq_getD] using hp.1
    have hq0 : q.getD 0 g = g := by simpa only [← List.headD_eq_getD] using hq.1
    simp only [padded,hiv,he,Nat.mod_self,hp0,hq0]
    simpa only [List.getD_eq_default _ _ (by omega : p.length ≤ i.val+1),
      List.getD_eq_default _ _ (by omega : q.length ≤ i.val+1)] using h i.val

lemma step_strip {g : TriangleGroup} {p q : List TriangleGroup}
    (hs : PathStep p q) (hp : GoodPath g p) (hn : p.length ≤ N) :
    Strip (padded g p : Row N) (padded g q) := by
  have hq := (step_good hs g).1 hp
  have hlen : q.length ≤ p.length := by cases hs <;> simp
  apply strip_padded_of_nat hp hq hn (by omega)
  cases hs with
  | triangle l r h => exact triangle_strip_nat l r _ _ _ g h (goodPath_padded hp)
  | stutter l r a => exact stutter_strip_nat l r a g (goodPath_padded hp)

lemma homotopy_good {p q : List TriangleGroup} (h : PathHomotopy p q) (g : TriangleGroup) :
    GoodPath g p ↔ GoodPath g q := by
  induction h with
  | rel a b h => exact step_good h g
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- A legal path homotopy is realizable on every sufficiently wide cyclic grid.
All extra columns are repeated base vertices. -/
theorem path_grid {p q : List TriangleGroup} (h : PathHomotopy p q) (g : TriangleGroup) :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N → GoodPath g p →
      ReflTransGen Strip (padded g p : Row (N+1)) (padded g q) := by
  induction h with
  | rel a b h =>
    exact ⟨a.length,fun N hN hp => .single (step_strip h hp (by omega))⟩
  | refl a => exact ⟨0,fun _ _ _ => .refl⟩
  | symm a b h ih =>
    obtain ⟨B,hB⟩ := ih
    exact ⟨B,fun N hN hp => strip_reach_reverse (hB N hN ((homotopy_good h g).2 hp))⟩
  | trans a b c h1 h2 ih1 ih2 =>
    obtain ⟨B1,hB1⟩ := ih1
    obtain ⟨B2,hB2⟩ := ih2
    exact ⟨max B1 B2,fun N hN hp => (hB1 N (by omega) hp).trans
      (hB2 N (by omega) ((homotopy_good h1 g).1 hp))⟩

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open Relation

lemma walk_append_chain (g : TriangleGroup) (w : List Letter) :
    List.IsChain Edge (walk g w ++ [g*eval (FreeMonoid.ofList w)]) := by
  induction w generalizing g with
  | nil => simp [walk,edge_refl]
  | cons s w ih =>
    have hi := ih (g*signed s)
    have hh : (walk (g*signed s) w ++ [g*eval (FreeMonoid.ofList (s::w))]).head? = some (g*signed s) := by
      cases w <;> rfl
    rw [walk,List.cons_append,List.isChain_cons]
    constructor
    · intro y hy
      simp only [hh,Option.mem_def,Option.some.injEq] at hy
      rw [← hy]
      exact legal_signed g s
    · simpa [eval,mul_assoc] using hi

lemma walk_good (g : TriangleGroup) (w : Word) (h : eval w = 1) : GoodPath g (walk g w.toList) := by
  constructor
  · cases hw : w.toList <;> rfl
  · simpa only [FreeMonoid.ofList_toList,h,mul_one] using walk_append_chain g w.toList

variable {N : ℕ} [NeZero N]

lemma reachable_sequence {x y : Row N} (h : ReflTransGen Strip x y) (hx : RowGood x) :
    ∃ L : ℕ, ∃ f : ℕ → Row N, f 0 = x ∧ (∀ i, L ≤ i → f i = y) ∧ ∀ i, Strip (f i) (f (i+1)) := by
  induction h with
  | refl => exact ⟨0,fun _ => x,rfl,fun _ _ => rfl,fun _ => strip_refl hx⟩
  | @tail y z h hs ih =>
    obtain ⟨L,f,h0,hL,hf⟩ := ih
    let f' : ℕ → Row N := fun i => if i ≤ L then f i else z
    refine ⟨L+1,f',?_,?_,?_⟩
    · simpa [f'] using h0
    · intro i hi; simp [f',show ¬i ≤ L by omega]
    · intro i
      by_cases hi : i < L
      · simpa only [f',ite_eq_left (show i ≤ L by omega),ite_eq_left (show i+1 ≤ L by omega)] using hf i
      · by_cases he : i = L
        · subst i
          simpa only [f',ite_eq_left (le_refl _),ite_eq_right (show ¬L+1 ≤ L by omega),hL L (le_refl _)] using hs
        · simpa only [f',ite_eq_right (show ¬i ≤ L by omega),ite_eq_right (show ¬i+1 ≤ L by omega)] using
            strip_refl (strip_good hs).2

lemma Legal.target {a b c : TriangleGroup} (h : Legal a b c) (v : Fin 3 → TriangleGroup)
    (h0 : v 0 = a) (h1 : v 1 = b) (h2 : v 2 = c) :
    ∃ t : TargetTriangle, ∀ i, ∃ j, t.vertex j = v i := by
  obtain ⟨t,i,j,k,hi,hj,hk⟩ := h
  refine ⟨t,?_⟩
  intro s
  fin_cases s
  · exact ⟨i,hi.trans h0.symm⟩
  · exact ⟨j,hj.trans h1.symm⟩
  · exact ⟨k,hk.trans h2.symm⟩

noncomputable def gridLabels (H : ℕ) (g : TriangleGroup) (f : ℕ → Row N) : GridDisk.Vertex H N → TriangleGroup
  | Sum.inl (r,i) => f r.val i
  | Sum.inr _ => g

lemma gridLabels_legal (H : ℕ) (g : TriangleGroup) (f : ℕ → Row N)
    (h0 : f 0 = fun _ => g) (hf : ∀ i, Strip (f i) (f (i+1))) :
    ∀ a : GridDisk.Face H N, ∃ t : TargetTriangle, ∀ k, ∃ j,
      t.vertex j = gridLabels H g f ((GridDisk.patch H N).tail (a,k)) := by
  intro a
  rcases a with ⟨r,i,b⟩ | i
  · cases b
    · apply ((hf r.val i).1).target
      all_goals simp [gridLabels,GridDisk.patch,GridDisk.tail]
    · apply ((hf r.val i).2).target
      all_goals simp [gridLabels,GridDisk.patch,GridDisk.tail]
  · apply (Legal.constant g).target
    all_goals simp [gridLabels,GridDisk.patch,GridDisk.tail,h0]

/-- Every null original-generator loop has legal grid fillings of all
sufficiently large widths. The entire disk is actual labelled triangles. -/
theorem null_grid (g : TriangleGroup) (w : Word) (hw : eval w = 1) :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N → ∃ H : ℕ, ∃ v : GridDisk.Vertex H (N+1) → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = (walk g w.toList).getD i.val g) ∧
      (∀ a : GridDisk.Face H (N+1), ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H (N+1)).tail (a,k))) := by
  obtain ⟨B,hB⟩ := path_grid (null_path w hw g) g
  refine ⟨B,fun N hN => ?_⟩
  have hc : (padded g [g] : Row (N+1)) = fun _ => g := by
    funext i
    by_cases hi : i.val = 0
    · simp [padded,hi]
    · rw [padded,List.getD_eq_default _ _ (by simp; omega)]
  have hg : RowGood (fun _ : Fin (N+1) => g) := fun _ => edge_refl g
  have hs := strip_reach_reverse (hB N hN (walk_good g w hw))
  rw [hc] at hs
  obtain ⟨L,f,h0,hL,hf⟩ := reachable_sequence hs hg
  refine ⟨L,gridLabels L g f,?_,gridLabels_legal L g f h0 hf⟩
  intro i
  change f (L+1) i = _
  rw [hL (L+1) (by omega)]
  rfl

end ArtinCAT0.WordDiagram

namespace ArtinCAT0
section CommutingOrbit
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

/-- A common minimizing point for two commuting elements, obtained by applying
semisimplicity inside the first minimum set. No flat-torus theorem is assumed. -/
lemma commuting_minimizer (hG : GeometricAction G X) (y : X) {g h : G}
    (hc : Commute g h) : ∃ x : X,
      dist x (g • x) = stableLengthAt y g ∧ dist x (h • x) = stableLengthAt y h := by
  classical
  let A := stableLengthAt y g
  let q : Unit → G := fun _ => g
  obtain ⟨z,hz⟩ := exists_displacement_minimizer hG g
  have hzA : dist z (g • z) = A := by
    rw [← stableLength_minimizer hG.1 hG.2.1 g hz]
    exact stableLength_basepoint hG.2.1 z y g
  let C := displacementSublevel (X := X) q A
  have hA : 0 ≤ A := stableLength_nonneg hG.2.1 y g
  let : Nonempty C := ⟨⟨z,fun _ => hzA.le⟩⟩
  let : ProperSpace C := sublevel_properSpace hG.2.1 q A
  let := sublevelAction hG.2.1 q A
  have hCG := geometric_tupleCentralizer hG q A hA
  let h' : tupleCentralizer q := ⟨h,fun _ => hc.symm⟩
  obtain ⟨x,hx⟩ := exists_displacement_minimizer hCG h'
  have hlen := stableLength_minimizer hCG.1 hCG.2.1 h' hx
  refine ⟨x.val,le_antisymm (x.property ()) ?_,?_⟩
  · rw [← stableLength_basepoint hG.2.1 x.val y g]
    exact stableLength_le_displacement hG.2.1 x.val g
  · change dist x (h' • x) = _
    rw [← hlen,sublevelAction_stableLength hG.2.1 q A x h']
    exact stableLength_basepoint hG.2.1 x.val y h

omit [ProperSpace X] [Nonempty X] in
lemma minimizer_of_length_eq (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (x y : X) (g : G) (hx : dist x (g • x) = stableLengthAt y g) :
    ∀ z : X, dist x (g • x) ≤ dist z (g • z) := by
  intro z
  rw [hx,← stableLength_basepoint hi z y g]
  exact stableLength_le_displacement hi z g

omit [ProperSpace X] [Nonempty X] in
lemma minimizer_zpow (hG : GeometricAction G X) (x : X) (g : G)
    (hx : ∀ z : X, dist x (g • x) ≤ dist z (g • z)) (i : ℤ) :
    dist x ((g^i) • x) = stableLengthAt x (g^i) := by
  cases i with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast,zpow_natCast,stableLength_pow hG.2.1,
      stableLength_minimizer hG.1 hG.2.1 g hx]
    exact minimizer_displacement_pow hG.1 hG.2.1 g hx n
  | negSucc n =>
    rw [zpow_negSucc,displacement_inv hG.2.1,stableLength_inv hG.2.1,
      stableLength_pow hG.2.1,stableLength_minimizer hG.1 hG.2.1 g hx]
    exact minimizer_displacement_pow hG.1 hG.2.1 g hx (n+1)

omit [ProperSpace X] [Nonempty X] in
lemma commuting_minimizer_product (hG : GeometricAction G X) (x : X) {g h : G}
    (hc : Commute g h)
    (hg : dist x (g • x) = stableLengthAt x g)
    (hh : dist x (h • x) = stableLengthAt x h) :
    dist x ((g*h) • x) = stableLengthAt x (g*h) := by
  have hq := commuting_displacement_quadrilateral hG.1 hG.2.1 x hc
  have hl := length_parallelogram hG.1 hG.2.1 x hc
  have ha := stableLength_le_displacement hG.2.1 x (g*h)
  have hb := stableLength_le_displacement hG.2.1 x (g*h⁻¹)
  have hn := stableLength_nonneg hG.2.1 x (g*h)
  have hm := stableLength_nonneg hG.2.1 x (g*h⁻¹)
  rw [hg,hh] at hq
  nlinarith [dist_nonneg (x := x) (y := (g*h) • x),
    dist_nonneg (x := x) (y := (g*h⁻¹) • x)]

theorem commuting_orbit_uniform (hG : GeometricAction G X) (y : X) {g h : G}
    (hc : Commute g h) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : ℤ,
      |dist y ((g^i*h^j) • y) - stableLengthAt y (g^i*h^j)| ≤ C := by
  obtain ⟨x,hg,hh⟩ := commuting_minimizer hG y hc
  have hgm := minimizer_of_length_eq hG.2.1 x y g hg
  have hhm := minimizer_of_length_eq hG.2.1 x y h hh
  refine ⟨2*dist y x,by positivity,fun i j => ?_⟩
  have he := commuting_minimizer_product hG x (hc.zpow_zpow i j)
    (minimizer_zpow hG x g hgm i) (minimizer_zpow hG x h hhm j)
  rw [← stableLength_basepoint hG.2.1 x y (g^i*h^j),← he]
  have h1 := displacement_change_base hG.2.1 y x (g^i*h^j)
  have h2 := displacement_change_base hG.2.1 x y (g^i*h^j)
  rw [dist_comm x y] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end CommutingOrbit
end ArtinCAT0

namespace ArtinCAT0.WordDiagram
open Relation

lemma step_length {p q : List TriangleGroup} (h : PathStep p q) : q.length ≤ p.length := by
  cases h <;> simp

lemma deletions_length {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) : q.length ≤ p.length := by
  induction h with
  | refl => rfl
  | tail h1 h2 ih => exact (step_length h2).trans ih

lemma deletions_homotopy {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) : PathHomotopy p q := by
  induction h with
  | refl => exact .refl _
  | tail h1 h2 ih => exact .trans _ _ _ ih (.rel _ _ h2)

lemma deletions_context {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) (l r : List TriangleGroup) :
    ReflTransGen PathStep (l++p++r) (l++q++r) := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih => exact ih.tail (pathStep_context h2 l r)

variable {N : ℕ} [NeZero N]
lemma deletions_grid {g : TriangleGroup} {p q : List TriangleGroup}
    (h : ReflTransGen PathStep p q) (hp : GoodPath g p) (hn : p.length ≤ N) :
    ReflTransGen Strip (padded g p : Row N) (padded g q) := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih =>
    exact ih.tail (step_strip h2 ((homotopy_good (deletions_homotopy h1) g).1 hp)
      ((deletions_length h1).trans hn))

lemma fill_row (g : TriangleGroup) (x : Row N)
    (h : ReflTransGen Strip x (fun _ => g)) :
    ∃ H : ℕ, ∃ v : GridDisk.Vertex H N → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = x i) ∧
      (∀ a : GridDisk.Face H N, ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H N).tail (a,k))) := by
  have hg : RowGood (fun _ : Fin N => g) := fun _ => edge_refl g
  obtain ⟨L,f,h0,hL,hf⟩ := reachable_sequence (strip_reach_reverse h) hg
  refine ⟨L,gridLabels L g f,?_,gridLabels_legal L g f h0 hf⟩
  intro i
  change f (L+1) i = _
  rw [hL (L+1) (by omega)]

omit [NeZero N] in
lemma pad_singleton (g : TriangleGroup) : (padded g [g] : Row N) = fun _ => g := by
  funext i
  by_cases hi : i.val = 0
  · simp [padded,hi]
  · rw [padded,List.getD_eq_default _ _ (by simp; omega)]

/-- Padding a boundary by repeated vertices does not demand additional
uncontrolled width: the deletions themselves realize its prescribed boundary. -/
theorem refined_grid (g : TriangleGroup) (w : Word) (hw : eval w = 1) :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N → ∀ p : List TriangleGroup,
      ReflTransGen PathStep p (walk g w.toList) → p.length ≤ N+1 →
      ∃ H : ℕ, ∃ v : GridDisk.Vertex H (N+1) → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = p.getD i.val g) ∧
      (∀ a : GridDisk.Face H (N+1), ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H (N+1)).tail (a,k))) := by
  obtain ⟨B,hB⟩ := path_grid (null_path w hw g) g
  refine ⟨B,fun N hN p hp hlen => ?_⟩
  have hg := walk_good g w hw
  have hpGood := (homotopy_good (deletions_homotopy hp) g).2 hg
  have hs := (deletions_grid hp hpGood hlen).trans (hB N hN hg)
  rw [pad_singleton] at hs
  exact fill_row g (padded g p) hs

lemma walk_join (g : TriangleGroup) (u v : List Letter) :
    ReflTransGen PathStep (walk g u ++ walk (g*eval (FreeMonoid.ofList u)) v) (walk g (u++v)) := by
  induction u generalizing g with
  | nil =>
    cases v with
    | nil => simpa [walk] using ReflTransGen.single (PathStep.stutter [] [] g)
    | cons s v =>
      simpa [walk] using ReflTransGen.single (PathStep.stutter [] (walk (g*signed s) v) g)
  | cons s u ih =>
    simpa [walk,eval,mul_assoc] using deletions_context (ih (g*signed s)) [g] []

lemma repeat_contract (g : TriangleGroup) (k : ℕ) :
    ReflTransGen PathStep (List.replicate (k+1) g) [g] := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    apply ReflTransGen.trans _ ih
    simpa only [List.replicate_succ,List.nil_append,List.cons_append] using
      ReflTransGen.single (PathStep.stutter [] (List.replicate k g) g)

lemma walk_pad_contract (g : TriangleGroup) (w : List Letter) (k : ℕ) :
    ReflTransGen PathStep (walk g w ++ List.replicate k (g*eval (FreeMonoid.ofList w))) (walk g w) := by
  induction w generalizing g with
  | nil => simpa [walk,List.replicate_succ] using repeat_contract g k
  | cons s w ih =>
    simpa [walk,eval,mul_assoc] using deletions_context (ih (g*signed s)) [g] []

def sidePath (g : TriangleGroup) (w : Word) (K : ℕ) : List TriangleGroup :=
  walk g w.toList ++ List.replicate (K-(w.toList.length+1)) (g*eval w)

lemma sidePath_contract (g : TriangleGroup) (w : Word) (K : ℕ) :
    ReflTransGen PathStep (sidePath g w K) (walk g w.toList) :=
  walk_pad_contract g w.toList (K-(w.toList.length+1))

lemma walk_length (g : TriangleGroup) (w : List Letter) : (walk g w).length = w.length+1 := by
  induction w generalizing g with
  | nil => rfl
  | cons s w ih => simp [walk,ih]

lemma sidePath_length (g : TriangleGroup) (w : Word) (K : ℕ) (h : w.toList.length+1 ≤ K) :
    (sidePath g w K).length = K := by
  simp only [sidePath,List.length_append,List.length_replicate,walk_length]
  omega

def triangleBoundary (g : TriangleGroup) (u v w : Word) (K : ℕ) : List TriangleGroup :=
  sidePath g u K ++ sidePath (g*eval u) v K ++ sidePath (g*eval u*eval v) w K

lemma triangleBoundary_contract (g : TriangleGroup) (u v w : Word) (K : ℕ) :
    ReflTransGen PathStep (triangleBoundary g u v w K) (walk g (u*v*w).toList) := by
  have h1 := deletions_context (sidePath_contract g u K) []
    (sidePath (g*eval u) v K ++ sidePath (g*eval u*eval v) w K)
  have h2 := deletions_context (sidePath_contract (g*eval u) v K) (walk g u.toList)
    (sidePath (g*eval u*eval v) w K)
  have h3 := deletions_context (sidePath_contract (g*eval u*eval v) w K)
    (walk g u.toList ++ walk (g*eval u) v.toList) []
  have h4 := deletions_context (walk_join g u.toList v.toList) [] (walk (g*eval u*eval v) w.toList)
  have h5 := walk_join g (u*v).toList w.toList
  have h12 := h1.trans (by simpa [List.append_assoc] using h2)
  have h123 := h12.trans (by simpa [List.append_assoc] using h3)
  have h1234 := h123.trans (by simpa [List.append_assoc] using h4)
  simpa [triangleBoundary,List.append_assoc,mul_assoc] using
    h1234.trans (by simpa [mul_assoc] using h5)

lemma triangleBoundary_length (g : TriangleGroup) (u v w : Word) (K : ℕ)
    (hu : u.toList.length+1 ≤ K) (hv : v.toList.length+1 ≤ K) (hw : w.toList.length+1 ≤ K) :
    (triangleBoundary g u v w K).length = 3*K := by
  simp only [triangleBoundary,List.length_append,sidePath_length _ _ _ hu,
    sidePath_length _ _ _ hv,sidePath_length _ _ _ hw]
  omega

lemma fill_row_tall (g : TriangleGroup) (x : Row N)
    (h : ReflTransGen Strip x (fun _ => g)) :
    ∃ L : ℕ, ∀ H : ℕ, L ≤ H → ∃ v : GridDisk.Vertex H N → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = x i) ∧
      (∀ a : GridDisk.Face H N, ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v ((GridDisk.patch H N).tail (a,k))) := by
  have hg : RowGood (fun _ : Fin N => g) := fun _ => edge_refl g
  obtain ⟨L,f,h0,hL,hf⟩ := reachable_sequence (strip_reach_reverse h) hg
  refine ⟨L,fun H hH => ⟨gridLabels H g f,?_,gridLabels_legal H g f h0 hf⟩⟩
  intro i
  change f (H+1) i = _
  rw [hL (H+1) (by omega)]

lemma PathStep.reverse {p q : List TriangleGroup} (h : PathStep p q) :
    PathStep p.reverse q.reverse := by
  cases h with
  | triangle l r h =>
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,
      List.nil_append,List.cons_append] using PathStep.triangle r.reverse l.reverse (Legal.swap _ _ _ h)
  | stutter l r g =>
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,
      List.nil_append,List.cons_append] using PathStep.stutter r.reverse l.reverse g

lemma deletions_reverse {p q : List TriangleGroup} (h : ReflTransGen PathStep p q) :
    ReflTransGen PathStep p.reverse q.reverse := by
  induction h with
  | refl => exact .refl
  | tail h1 h2 ih => exact ih.tail h2.reverse

def inverseLetter (s : Letter) : Letter := (s.1,!s.2)
def inverseLetters (l : List Letter) : List Letter := l.reverse.map inverseLetter

@[simp] lemma signed_inverseLetter (s : Letter) : signed (inverseLetter s) = (signed s)⁻¹ := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [signed,inverseLetter]

@[simp] lemma inverseLetters_cons (s : Letter) (l : List Letter) :
    inverseLetters (s::l) = inverseLetters l ++ [inverseLetter s] := by
  simp [inverseLetters]

@[simp] lemma eval_inverseLetters (l : List Letter) :
    eval (FreeMonoid.ofList (inverseLetters l)) = (eval (FreeMonoid.ofList l))⁻¹ := by
  induction l with
  | nil => simp [inverseLetters,eval]
  | cons s l ih =>
    rw [inverseLetters_cons,FreeMonoid.ofList_append,map_mul,ih,eval_cons]
    simp [eval]

lemma walk_last_append (g : TriangleGroup) (l : List Letter) :
    (walk g l).dropLast ++ [g*eval (FreeMonoid.ofList l)] = walk g l := by
  simpa [walk] using (walk_append g l []).symm

lemma walk_append_one (g : TriangleGroup) (l : List Letter) (s : Letter) :
    walk g (l++[s]) = walk g l ++ [g*eval (FreeMonoid.ofList l)*signed s] := by
  rw [walk_append]
  change (walk g l).dropLast ++ ([g*eval (FreeMonoid.ofList l)] ++
      [g*eval (FreeMonoid.ofList l)*signed s]) = _
  rw [← List.append_assoc,walk_last_append]

lemma walk_reverse (g : TriangleGroup) (l : List Letter) :
    (walk g l).reverse = walk (g*eval (FreeMonoid.ofList l)) (inverseLetters l) := by
  induction l generalizing g with
  | nil => simp [walk,inverseLetters]
  | cons s l ih =>
    simp only [walk,List.reverse_cons,ih,inverseLetters_cons,walk_append_one,eval_cons]
    congr 1
    · rw [mul_assoc]
    · simp only [eval_inverseLetters,signed_inverseLetter]
      congr 1
      group

lemma repeat_pre_contract (g : TriangleGroup) (w : List Letter) (k : ℕ) :
    ReflTransGen PathStep (List.replicate k g ++ walk g w) (walk g w) := by
  cases w with
  | nil => simpa [walk,List.replicate_succ',List.append_assoc] using repeat_contract g k
  | cons s w =>
    have h := deletions_context (repeat_contract g k) [] (walk (g*signed s) w)
    simpa [walk,List.replicate_succ',List.append_assoc] using h

/-- Extra endpoint stutters allow either orientation to be trimmed while
retaining both endpoints. This ensures exact shared-edge parametrizations. -/
def fullSide (g : TriangleGroup) (w : Word) (K : ℕ) : List TriangleGroup :=
  [g] ++ walk g w.toList ++ List.replicate (K-(w.toList.length+1)) (g*eval w)

lemma fullSide_length (g : TriangleGroup) (w : Word) (K : ℕ)
    (h : w.toList.length+1 ≤ K) : (fullSide g w K).length = K+1 := by
  simp only [fullSide,List.length_append,List.length_replicate,walk_length,List.length_singleton]
  omega

lemma fullSide_trim_forward (g : TriangleGroup) (w : Word) (K : ℕ)
    (h : w.toList.length+2 ≤ K) :
    ReflTransGen PathStep (fullSide g w K).dropLast (walk g w.toList) := by
  have hk : K-(w.toList.length+1) = (K-(w.toList.length+2))+1 := by omega
  simp only [fullSide,hk,List.replicate_succ',← List.append_assoc,List.dropLast_concat]
  have h1 := deletions_context (repeat_pre_contract g w.toList 1) []
    (List.replicate (K-(w.toList.length+2)) (g*eval w))
  apply ReflTransGen.trans _ (walk_pad_contract g w.toList (K-(w.toList.length+2)))
  simpa using h1

lemma fullSide_trim_reverse (g : TriangleGroup) (w : Word) (K : ℕ) :
    ReflTransGen PathStep (fullSide g w K).reverse.dropLast
      (walk (g*eval w) (inverseLetters w.toList)) := by
  simp only [fullSide,List.reverse_append,List.reverse_replicate,List.reverse_singleton,
    ← List.append_assoc,List.dropLast_concat]
  rw [walk_reverse]
  simpa only [FreeMonoid.ofList_toList] using repeat_pre_contract (g*eval w) (inverseLetters w.toList) (K-(w.toList.length+1))

end ArtinCAT0.WordDiagram

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0.SectorMetric
open Complex
abbrev Point := ℝ × ℝ

noncomputable def vec (c : ℝ) (p : Point) : ℂ :=
  (p.1 + c*p.2) + (Real.sqrt (1-c^2)*p.2)*I

@[simp] lemma vec_zero (c : ℝ) : vec c (0,0) = 0 := by simp [vec]
lemma vec_add (c : ℝ) (p q : Point) : vec c (p.1+q.1,p.2+q.2) = vec c p + vec c q := by
  simp only [vec,ofReal_add]
  ring
lemma vec_sub (c : ℝ) (p q : Point) : vec c (p.1-q.1,p.2-q.2) = vec c p - vec c q := by
  simp only [vec,ofReal_sub]
  ring
lemma vec_mul (c a : ℝ) (p : Point) : vec c (a*p.1,a*p.2) = (a : ℂ)*vec c p := by
  simp only [vec,ofReal_mul]
  ring

lemma vec_sq (c : ℝ) (hc : |c| ≤ 1) (p : Point) :
    ‖vec c p‖^2 = p.1^2+p.2^2+2*c*p.1*p.2 := by
  have hcs : 0 ≤ 1-c^2 := by nlinarith [sq_abs c,abs_nonneg c]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [vec,Complex.normSq_apply,add_re,ofReal_re,mul_re,I_re,ofReal_im,I_im,
    zero_mul,mul_zero,sub_zero,add_zero,add_im,mul_im,zero_add,ofReal_im]
  nlinarith [Real.sq_sqrt hcs]

lemma vec_basis1 (c : ℝ) : ‖vec c (1,0)‖ = 1 := by simp [vec]
lemma vec_basis2 (c : ℝ) (hc : |c| ≤ 1) : ‖vec c (0,1)‖ = 1 := by
  have h := vec_sq c hc (0,1)
  have hs : ‖vec c (0,1)‖^2 = 1 := by simpa only [zero_pow (by decide : 2 ≠ 0),one_pow,mul_zero,zero_mul,zero_add,add_zero] using h
  nlinarith [norm_nonneg (vec c (0,1))]

lemma vec_bound (c : ℝ) (hc : |c| ≤ 1) (p : Point) : ‖vec c p‖ ≤ |p.1|+|p.2| := by
  have he : vec c p = (p.1 : ℂ)*vec c (1,0)+(p.2 : ℂ)*vec c (0,1) := by
    simp [vec]
    ring
  rw [he]
  calc
    _ ≤ ‖(p.1 : ℂ)*vec c (1,0)‖ + ‖(p.2 : ℂ)*vec c (0,1)‖ := norm_add_le _ _
    _ = _ := by simp [vec_basis1,vec_basis2 c hc,Complex.norm_real,Real.norm_eq_abs]

lemma vec_lipschitz (c : ℝ) (hc : |c| ≤ 1) (p q : Point) :
    |‖vec c p‖-‖vec c q‖| ≤ |p.1-q.1|+|p.2-q.2| := by
  calc
    _ ≤ ‖vec c p-vec c q‖ := abs_norm_sub_norm_le _ _
    _ = ‖vec c (p.1-q.1,p.2-q.2)‖ := congrArg norm (vec_sub c p q).symm
    _ ≤ _ := vec_bound c hc _

noncomputable def mixNorm (c t : ℝ) : ℝ := ‖vec c (1-t,t)‖
noncomputable def unit (c t : ℝ) : Point := ((1-t)/mixNorm c t,t/mixNorm c t)

lemma mixNorm_bounds {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    1/2 ≤ mixNorm c t ∧ mixNorm c t ≤ 1 := by
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have hsq := vec_sq c hca (1-t,t)
  have hnon : 0 ≤ mixNorm c t := norm_nonneg _
  constructor
  · have hre : (vec c (1-t,t)).re = 1-t+c*t := by simp [vec]
    have hr := Complex.re_le_norm (vec c (1-t,t))
    rw [hre] at hr
    dsimp only [mixNorm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) ht.1]
  · have h := vec_bound c hca (1-t,t)
    simpa only [mixNorm,abs_of_nonneg ht.1,abs_of_nonneg (sub_nonneg.mpr ht.2),sub_add_cancel] using h

lemma unit_vec {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    ‖vec c (unit c t)‖ = 1 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  simp only [unit,div_eq_mul_inv]
  rw [mul_comm (1-t),mul_comm t]
  rw [vec_mul c (mixNorm c t)⁻¹ (1-t,t),norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ (ne_of_gt hp)

lemma unit_nonneg {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    0 ≤ (unit c t).1 ∧ 0 ≤ (unit c t).2 := by
  have hm := mixNorm_bounds hc hc' ht
  exact ⟨div_nonneg (sub_nonneg.mpr ht.2) (by linarith),div_nonneg ht.1 (by linarith)⟩

lemma unit_sum {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    1 ≤ (unit c t).1+(unit c t).2 ∧ (unit c t).1+(unit c t).2 ≤ 2 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  change 1 ≤ (1-t)/mixNorm c t+t/mixNorm c t ∧ (1-t)/mixNorm c t+t/mixNorm c t ≤ 2
  rw [← add_div,sub_add_cancel]
  constructor
  · exact (le_div_iff₀ hp).mpr (by linarith)
  · exact (div_le_iff₀ hp).mpr (by linarith)

lemma unit_pairing1 {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    c ≤ (unit c t).1+c*(unit c t).2 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  change c ≤ (1-t)/mixNorm c t+c*(t/mixNorm c t)
  rw [← mul_div_assoc,← add_div]
  apply (le_div_iff₀ hp).mpr
  have h1 : c*mixNorm c t ≤ c := mul_le_of_le_one_right (by linarith) hm.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hc') (sub_nonneg.mpr ht.2)]

lemma unit_pairing2 {c t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    c ≤ c*(unit c t).1+(unit c t).2 := by
  have hm := mixNorm_bounds hc hc' ht
  have hp : 0 < mixNorm c t := by linarith
  change c ≤ c*((1-t)/mixNorm c t)+t/mixNorm c t
  rw [← mul_div_assoc,← add_div]
  apply (le_div_iff₀ hp).mpr
  have h1 : c*mixNorm c t ≤ c := mul_le_of_le_one_right (by linarith) hm.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hc') ht.1]

/-- The short chord needed for the outside cap, with no trigonometry. -/
lemma detour_gap {c : ℝ} (hc : 1/2 < c) (hc' : c ≤ 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 0 < 1+r^2-2*c*r ∧
      2*Real.sqrt (1+r^2-2*c*r)+r < 2 := by
  let r := (2*c-1)/4
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 1/4 := by dsimp [r]; linarith
  have hpos : 0 < 1+r^2-2*c*r := by nlinarith
  have hs := Real.sq_sqrt hpos.le
  have hn := Real.sqrt_nonneg (1+r^2-2*c*r)
  have hcR : 4*r = 2*c-1 := by dsimp [r]; ring
  refine ⟨r,hr,by linarith,hpos,?_⟩
  nlinarith

lemma quotient_lipschitz {a b u v : ℝ} (_ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hu : 1/2 ≤ u) (hv : 1/2 ≤ v) :
    |a/u-b/v| ≤ 2*|a-b|+4*|u-v| := by
  have hup : 0 < u := by linarith
  have hvp : 0 < v := by linarith
  have he : a/u-b/v = (a-b)/u+b*(v-u)/(u*v) := by field_simp; ring
  rw [he]
  calc
    _ ≤ |(a-b)/u|+|b*(v-u)/(u*v)| := abs_add_le _ _
    _ = |a-b|/u + |b| * |u-v|/(u*v) := by
      rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hup,abs_of_pos hvp,abs_sub_comm v u]
    _ ≤ 2*|a-b|+4*|u-v| := by
      have h1 : |a-b|/u ≤ 2*|a-b| := (div_le_iff₀ hup).mpr (by nlinarith [abs_nonneg (a-b)])
      have huv : 1/4 ≤ u*v := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
      have h2 : |b| * |u-v|/(u*v) ≤ 4*|u-v| :=
        (div_le_iff₀ (mul_pos hup hvp)).mpr (by nlinarith [abs_nonneg (u-v)])
      linarith

lemma mixNorm_lipschitz {c : ℝ} (hc : |c| ≤ 1) (s t : ℝ) :
    |mixNorm c s-mixNorm c t| ≤ 2*|s-t| := by
  have h := vec_lipschitz c hc (1-s,s) (1-t,t)
  have he : (1-s)-(1-t) = -(s-t) := by ring
  simpa only [mixNorm,he,abs_neg,two_mul] using h

lemma unit_lipschitz {c s t : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    |(unit c s).1-(unit c t).1| ≤ 10*|s-t| ∧
    |(unit c s).2-(unit c t).2| ≤ 10*|s-t| := by
  have hms := (mixNorm_bounds hc hc' hs).1
  have hmt := (mixNorm_bounds hc hc' ht).1
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have hm := mixNorm_lipschitz hca s t
  have h0 := quotient_lipschitz
    (show |1-s| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]; linarith [hs.1])
    (show |1-t| ≤ 1 by rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]) hms hmt
  have h1 := quotient_lipschitz (show |s| ≤ 1 by simpa only [abs_of_nonneg hs.1] using hs.2)
    (show |t| ≤ 1 by simpa only [abs_of_nonneg ht.1] using ht.2) hms hmt
  have he : (1-s)-(1-t) = -(s-t) := by ring
  rw [he,abs_neg] at h0
  exact ⟨by change |(1-s)/mixNorm c s-(1-t)/mixNorm c t| ≤ _; linarith,
    by change |s/mixNorm c s-t/mixNorm c t| ≤ _; linarith⟩

@[simp] lemma unit_zero (c : ℝ) : unit c 0 = (1,0) := by simp [unit,mixNorm,vec]
@[simp] lemma unit_one (c : ℝ) (hc : |c| ≤ 1) : unit c 1 = (0,1) := by
  simp only [unit,mixNorm,sub_self,vec_basis2 c hc,div_one]

lemma chord_axis1 {c t r : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1)
    (ht : t ∈ Set.Icc 0 1) (hr : 0 ≤ r) :
    ‖vec c ((unit c t).1-r,(unit c t).2)‖^2 ≤ 1+r^2-2*c*r := by
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have h1 := vec_sq c hca (unit c t)
  rw [unit_vec hc hc' ht] at h1
  rw [vec_sq c hca]
  nlinarith [mul_nonneg hr (sub_nonneg.mpr (unit_pairing1 hc hc' ht))]

lemma chord_axis2 {c t r : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 1)
    (ht : t ∈ Set.Icc 0 1) (hr : 0 ≤ r) :
    ‖vec c ((unit c t).1,(unit c t).2-r)‖^2 ≤ 1+r^2-2*c*r := by
  have hca : |c| ≤ 1 := abs_le.mpr ⟨by linarith,hc'⟩
  have h1 := vec_sq c hca (unit c t)
  rw [unit_vec hc hc' ht] at h1
  rw [vec_sq c hca]
  nlinarith [mul_nonneg hr (sub_nonneg.mpr (unit_pairing2 hc hc' ht))]

end ArtinCAT0.SectorMetric

namespace ArtinCAT0
section PairingCauchy
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

lemma lengthPairing_abs_le (hG : GeometricAction G X) (y : X) {g h : G} (hc : Commute g h) :
    |lengthPairing y g h| ≤ stableLengthAt y g * stableLengthAt y h := by
  by_cases hz : stableLengthAt y g = 0
  · rw [hz,zero_mul,lengthPairing_zero_of_length_zero hG.1 hG.2.1 y hc hz,abs_zero]
  · have hp : 0 < stableLengthAt y g := lt_of_le_of_ne (stableLength_nonneg hG.2.1 y g) (Ne.symm hz)
    obtain ⟨x,hx⟩ := exists_displacement_minimizer hG g
    have hxL : dist x (g • x) = stableLengthAt y g := by
      rw [← stableLength_minimizer hG.1 hG.2.1 g hx]
      exact stableLength_basepoint hG.2.1 x y g
    have ha (n : ℕ) : dist x ((g^n) • x) = n*stableLengthAt y g := by
      rw [minimizer_displacement_pow hG.1 hG.2.1 g hx,hxL]
    rw [← lengthPairing_basepoint hG.2.1 x y g h,
      lengthPairing_eq_orbitCharacter hG.1 hG.2.1 x g _ hp ha
        (stableLength_basepoint hG.2.1 x y g) hc,abs_mul,abs_of_pos hp]
    rw [← stableLength_basepoint hG.2.1 x y h]
    exact mul_le_mul_of_nonneg_left (orbitCharacter_abs_le hG.1 hG.2.1 x g _ hp ha hc) hp.le

end PairingCauchy

section BraidThree
variable {G : Type*} [Group G] {a b : G}

def twoBraid (a b : G) (i : ℕ) : G := if i = 0 then a else b
lemma twoBraid_relations (h : a*b*a = b*a*b) : BraidRelations 2 (twoBraid a b) := by
  constructor
  · intro i hi
    have he : i = 0 := by omega
    subst i
    simpa [twoBraid] using h
  · intro i j hi hj hij
    omega

lemma braid_three_commute (h : a*b*a = b*a*b) : Commute a ((a*b)^3) ∧ Commute b ((a*b)^3) := by
  have hc (i : ℕ) (hi : i < 2) := braidCenter_commute (twoBraid_relations h) (by omega : 2 ≤ 2) hi
  have he : braidCenter (twoBraid a b) 2 = (a*b)^3 := by
    simpa [twoBraid] using braidCenter_two (s := twoBraid a b) (by simpa [twoBraid] using h)
  exact ⟨by simpa [he,twoBraid] using hc 0 (by decide),
    by simpa [he,twoBraid] using hc 1 (by decide)⟩

variable {X : Type*} [MetricSpace X] [MulAction G X] [ProperSpace X] [Nonempty X]
lemma braid_three_pairing (hG : GeometricAction G X) (y : X) (h : a*b*a = b*a*b) :
    lengthPairing y (a^2) ((a*b)^3) = stableLengthAt y ((a*b)^3)^2/3 ∧
    lengthPairing y (b^2) ((a*b)^3) = stableLengthAt y ((a*b)^3)^2/3 := by
  have hs := twoBraid_relations h
  have he : braidCenter (twoBraid a b) 2 = (a*b)^3 := by
    simpa [twoBraid] using braidCenter_two (s := twoBraid a b) (by simpa [twoBraid] using h)
  have h0 := braidCenter_length_sq hG y hs (by omega : 2 ≤ 2) (by decide : 0 < 2)
  have h1 := braidCenter_length_sq hG y hs (by omega : 2 ≤ 2) (by decide : 1 < 2)
  simp only [he,twoBraid,ite_true,show ¬(1 = (0 : ℕ)) by decide,ite_false] at h0 h1
  have hc := braid_three_commute h
  rw [lengthPairing_pow_left hG.1 hG.2.1 y hc.1,
    lengthPairing_pow_left hG.1 hG.2.1 y hc.2]
  norm_num at h0 h1 ⊢
  constructor <;> linarith
end BraidThree

namespace SixSector

def ray (i : Fin 6) : TriangleGroup :=
  if i.val % 2 = 0 then triangleGen ⟨i.val/2,by omega⟩ ^ 2
    else triangleH ⟨i.val/2,by omega⟩ ^ 3

lemma ray_even (i : Fin 3) : ray ⟨2*i.val,by omega⟩ = triangleGen i ^ 2 := by
  simp only [ray,Nat.mul_mod_right,ite_true]
  congr 2
  apply Fin.ext
  change 2*i.val/2 = i.val
  omega
lemma ray_odd (i : Fin 3) : ray ⟨2*i.val+1,by omega⟩ = triangleH i ^ 3 := by
  simp only [ray,show (2*i.val+1)%2 = 1 by omega,show ¬(1 = (0 : ℕ)) by decide,ite_false]
  congr 2
  apply Fin.ext
  change (2*i.val+1)/2 = i.val
  omega

lemma ray_commute (i : Fin 6) : Commute (ray i) (ray (i+1)) := by
  have h0 := braid_three_commute (triangle_braid 0)
  have h1 := braid_three_commute (triangle_braid 1)
  have h2 := braid_three_commute (triangle_braid 2)
  fin_cases i
  · exact h0.1.pow_left 2
  · exact (h0.2.pow_left 2).symm
  · exact h1.1.pow_left 2
  · exact (h1.2.pow_left 2).symm
  · exact h2.1.pow_left 2
  · exact (h2.2.pow_left 2).symm

section Action
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

lemma generator_square_length_pos (hG : GeometricAction TriangleGroup X) (y : X) (i : Fin 3) :
    0 < stableLengthAt y (triangleGen i ^ 2) := by
  have hp : 0 < stableLengthAt y (triangleGen i) := by
    apply lt_of_le_of_ne (stableLength_nonneg hG.2.1 y _)
    intro h
    exact triangle_generator_infinite_order i ((stableLength_eq_zero_iff_finiteOrder hG y _).mp h.symm)
  rw [stableLength_pow hG.2.1]
  positivity

omit [ProperSpace X] [Nonempty X] in
lemma adjacent_square_length (hG : GeometricAction TriangleGroup X) (y : X) (i : Fin 3) :
    stableLengthAt y (triangleGen (i+1)^2) = stableLengthAt y (triangleGen i^2) := by
  rw [stableLength_pow hG.2.1,stableLength_pow hG.2.1,← braid_conjugate (triangle_braid i),
    stableLength_conjugate hG.2.1]

def StrictRatios (y : X) : Prop := ∀ i : Fin 3,
  (1 : ℝ)/2 < stableLengthAt y (triangleH i^3)/(3*stableLengthAt y (triangleGen i^2))

lemma ray_length_pos (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    0 < stableLengthAt y (ray i) := by
  have he k := generator_square_length_pos hG y k
  have ho k : 0 < stableLengthAt y (triangleH k^3) := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) (generator_square_length_pos hG y k) : 0 < 3*stableLengthAt y (triangleGen k^2))).mp (hR k)
    linarith [he k]
  fin_cases i
  · exact he 0
  · exact ho 0
  · exact he 1
  · exact ho 1
  · exact he 2
  · exact ho 2

noncomputable def cosine (y : X) (i : Fin 6) : ℝ :=
  lengthPairing y (ray i) (ray (i+1))/(stableLengthAt y (ray i)*stableLengthAt y (ray (i+1)))

lemma cosine_lower (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    1/2 < cosine y i := by
  have hL k := ray_length_pos hG y hR k
  have hc (k : Fin 3) :
      lengthPairing y (triangleGen k^2) (triangleH k^3) = stableLengthAt y (triangleH k^3)^2/3 ∧
      lengthPairing y (triangleGen (k+1)^2) (triangleH k^3) = stableLengthAt y (triangleH k^3)^2/3 :=
    braid_three_pairing hG y (triangle_braid k)
  have hcomm (k : Fin 3) : Commute (triangleH k^3) (triangleGen (k+1)^2) :=
    ((braid_three_commute (triangle_braid k)).2.pow_left 2).symm
  have hp (k : Fin 3) : 3*stableLengthAt y (triangleGen k^2)/2 < stableLengthAt y (triangleH k^3) := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) (generator_square_length_pos hG y k) : 0 < 3*stableLengthAt y (triangleGen k^2))).mp (hR k)
    linarith
  have hnext k := adjacent_square_length hG y k
  unfold cosine
  apply (lt_div_iff₀ (mul_pos (hL i) (hL (i+1)))).mpr
  have hpair (k : Fin 3) :
      stableLengthAt y (triangleGen k^2)*stableLengthAt y (triangleH k^3)/2 <
        stableLengthAt y (triangleH k^3)^2/3 := by
    have hz := ray_length_pos hG y hR ⟨2*k.val+1,by omega⟩
    rw [ray_odd] at hz
    nlinarith [mul_pos (sub_pos.mpr (hp k)) hz]
  fin_cases i
  · change 1/2*(stableLengthAt y (triangleGen 0^2)*stableLengthAt y (triangleH 0^3)) <
      lengthPairing y (triangleGen 0^2) (triangleH 0^3)
    rw [(hc 0).1]
    linarith [hpair 0]
  · change 1/2*(stableLengthAt y (triangleH 0^3)*stableLengthAt y (triangleGen (0+1)^2)) <
      lengthPairing y (triangleH 0^3) (triangleGen (0+1)^2)
    rw [lengthPairing_symmetric y (hcomm 0),
      (hc 0).2,hnext 0]
    nlinarith [hpair 0]
  · change 1/2*(stableLengthAt y (triangleGen 1^2)*stableLengthAt y (triangleH 1^3)) <
      lengthPairing y (triangleGen 1^2) (triangleH 1^3)
    rw [(hc 1).1]
    linarith [hpair 1]
  · change 1/2*(stableLengthAt y (triangleH 1^3)*stableLengthAt y (triangleGen (1+1)^2)) <
      lengthPairing y (triangleH 1^3) (triangleGen (1+1)^2)
    rw [lengthPairing_symmetric y (hcomm 1),
      (hc 1).2,hnext 1]
    nlinarith [hpair 1]
  · change 1/2*(stableLengthAt y (triangleGen 2^2)*stableLengthAt y (triangleH 2^3)) <
      lengthPairing y (triangleGen 2^2) (triangleH 2^3)
    rw [(hc 2).1]
    linarith [hpair 2]
  · change 1/2*(stableLengthAt y (triangleH 2^3)*stableLengthAt y (triangleGen (2+1)^2)) <
      lengthPairing y (triangleH 2^3) (triangleGen (2+1)^2)
    rw [lengthPairing_symmetric y (hcomm 2),
      (hc 2).2,hnext 2]
    nlinarith [hpair 2]

lemma cosine_le_one (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    cosine y i ≤ 1 := by
  apply (div_le_iff₀ (mul_pos (ray_length_pos hG y hR i) (ray_length_pos hG y hR (i+1)))).mpr
  simpa only [one_mul] using
    (le_abs_self (lengthPairing y (ray i) (ray (i+1)))).trans (lengthPairing_abs_le hG y (ray_commute i))

end Action
end SixSector
end ArtinCAT0

namespace ArtinCAT0.SectorMetric

lemma floor_error {L : ℝ} (hL : 0<L) (x : ℝ) :
    |(⌊x/L⌋ : ℝ)*L-x| ≤ L := by
  have h1 : (⌊x/L⌋ : ℝ) ≤ x/L := Int.floor_le _
  have h2 : x/L < (⌊x/L⌋ : ℝ)+1 := Int.lt_floor_add_one _
  have h3 := (le_div_iff₀ hL).mp h1
  have h4 := (div_lt_iff₀ hL).mp h2
  rw [abs_of_nonpos (by linarith)]
  nlinarith

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
  [ProperSpace X] [Nonempty X]

noncomputable def lattice (g h : G) (L M : ℝ) (p : Point) : G :=
  g^⌊p.1/L⌋ * h^⌊p.2/M⌋

lemma lattice_origin (g h : G) (L M : ℝ) : lattice g h L M (0,0) = 1 := by
  simp [lattice]

lemma powers_difference {g h : G} (hc : Commute g h) (i j k l : ℤ) :
    (g^i*h^j)⁻¹*(g^k*h^l) = g^(k-i)*h^(l-j) := by
  calc
    _ = h^(-j) * g^(k-i) * h^l := by simp only [zpow_sub,zpow_neg]; group
    _ = g^(k-i) * h^(-j) * h^l := by rw [(hc.zpow_zpow (k-i) (-j)).eq]
    _ = _ := by simp only [zpow_sub,zpow_neg]; group

omit [ProperSpace X] [Nonempty X] in
lemma lattice_length (hG : GeometricAction G X) (y : X) {g h : G}
    (hcomm : Commute g h) {c : ℝ} (hc : |c| ≤ 1)
    (hp : lengthPairing y g h = c*stableLengthAt y g*stableLengthAt y h) (i j : ℤ) :
    stableLengthAt y (g^i*h^j) =
      ‖vec c ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h)‖ := by
  have he := stableLength_product_sq y (g^i) (h^j)
  rw [stableLength_zpow hG.2.1,stableLength_zpow hG.2.1,
    lengthPairing_zpow_left hG.1 hG.2.1 y (hcomm.zpow_right j),
    lengthPairing_zpow_right hG.1 hG.2.1 y hcomm,hp] at he
  have hv := vec_sq c hc ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h)
  have hsq : stableLengthAt y (g^i*h^j)^2 =
      ‖vec c ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h)‖^2 := by
    rw [he,hv]
    simp only [mul_pow,sq_abs]
    ring
  nlinarith [stableLength_nonneg hG.2.1 y (g^i*h^j),
    norm_nonneg (vec c ((i:ℝ)*stableLengthAt y g,(j:ℝ)*stableLengthAt y h))]

/-- Rounding a flat-coordinate lattice introduces a bounded additive metric
error, uniformly for all pairs of real points, not just a fixed finite net. -/
theorem lattice_metric (hG : GeometricAction G X) (y : X) {g h : G}
    (hg : 0<stableLengthAt y g) (hh : 0<stableLengthAt y h) (hcomm : Commute g h)
    {c : ℝ} (hc : |c|≤1)
    (hp : lengthPairing y g h = c*stableLengthAt y g*stableLengthAt y h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Point,
      |dist (lattice g h (stableLengthAt y g) (stableLengthAt y h) p • y)
          (lattice g h (stableLengthAt y g) (stableLengthAt y h) q • y) -
        ‖vec c (q.1-p.1,q.2-p.2)‖| ≤ C := by
  obtain ⟨C,hC,hbound⟩ := commuting_orbit_uniform hG y hcomm
  let L := stableLengthAt y g
  let M := stableLengthAt y h
  refine ⟨C+2*L+2*M,by dsimp [L,M]; positivity,?_⟩
  intro p q
  let i := ⌊p.1/L⌋; let j := ⌊p.2/M⌋
  let k := ⌊q.1/L⌋; let l := ⌊q.2/M⌋
  have h0 := hbound (k-i) (l-j)
  rw [lattice_length hG y hcomm hc hp] at h0
  have h1 := vec_lipschitz c hc (((k-i:ℤ):ℝ)*L,((l-j:ℤ):ℝ)*M) (q.1-p.1,q.2-p.2)
  have hx : |((k-i:ℤ):ℝ)*L-(q.1-p.1)| ≤ 2*L := by
    have hpi := floor_error hg p.1
    have hqk := floor_error hg q.1
    have he : ((k-i:ℤ):ℝ)*L-(q.1-p.1) = ((k:ℝ)*L-q.1)-((i:ℝ)*L-p.1) := by
      rw [Int.cast_sub]; ring
    rw [he]
    exact (abs_sub _ _).trans (by dsimp [i,k,L] at *; linarith)
  have hy : |((l-j:ℤ):ℝ)*M-(q.2-p.2)| ≤ 2*M := by
    have hpj := floor_error hh p.2
    have hql := floor_error hh q.2
    have he : ((l-j:ℤ):ℝ)*M-(q.2-p.2) = ((l:ℝ)*M-q.2)-((j:ℝ)*M-p.2) := by
      rw [Int.cast_sub]; ring
    rw [he]
    exact (abs_sub _ _).trans (by dsimp [j,l,M] at *; linarith)
  rw [action_dist hG.2.1]
  change |dist y (((g^i*h^j)⁻¹*(g^k*h^l)) • y)-_| ≤ _
  rw [powers_difference hcomm]
  calc
    _ ≤ |dist y ((g^(k-i)*h^(l-j)) • y)-‖vec c (((k-i:ℤ):ℝ)*L,((l-j:ℤ):ℝ)*M)‖| +
        |‖vec c (((k-i:ℤ):ℝ)*L,((l-j:ℤ):ℝ)*M)‖-‖vec c (q.1-p.1,q.2-p.2)‖| :=
      abs_sub_le _ _ _
    _ ≤ _ := by dsimp only [L,M] at *; linarith

end ArtinCAT0.SectorMetric

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0.WordDiagram
open Relation

abbrev Side := Word × Bool

def inverseWord (w : Word) : Word := FreeMonoid.ofList (inverseLetters w.toList)
def sideWord (s : Side) : Word := if s.2 then inverseWord s.1 else s.1
def sideFlip (s : Side) : Side := (s.1,!s.2)
noncomputable def sideFull (g : TriangleGroup) (s : Side) (K : ℕ) : List TriangleGroup :=
  if s.2 then (fullSide (g*(eval s.1)⁻¹) s.1 K).reverse else fullSide g s.1 K

@[simp] lemma eval_inverseWord (w : Word) : eval (inverseWord w) = (eval w)⁻¹ :=
  eval_inverseLetters w.toList

@[simp] lemma eval_sideFlip (s : Side) : eval (sideWord (sideFlip s)) = (eval (sideWord s))⁻¹ := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideWord,sideFlip]

lemma sideFull_reverse (g : TriangleGroup) (s : Side) (K : ℕ) :
    (sideFull g s K).reverse = sideFull (g*eval (sideWord s)) (sideFlip s) K := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,sideFlip,sideWord,mul_assoc]

lemma sideFull_length (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+1 ≤ K) :
    (sideFull g s K).length = K+1 := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,fullSide_length _ _ _ h]

lemma sideFull_contract (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+2 ≤ K) :
    ReflTransGen PathStep (sideFull g s K).dropLast (walk g (sideWord s).toList) := by
  rcases s with ⟨w,b⟩
  cases b
  · exact fullSide_trim_forward g w K h
  · simpa [sideWord,inverseWord,sideFull,mul_assoc] using
      fullSide_trim_reverse (g*(eval w)⁻¹) w K

lemma fullSide_head (g : TriangleGroup) (w : Word) (K : ℕ) :
    (fullSide g w K).head? = some g := by simp [fullSide]

lemma fullSide_last (g : TriangleGroup) (w : Word) (K : ℕ) (h : w.toList.length+2 ≤ K) :
    (fullSide g w K).getLast? = some (g*eval w) := by
  have hk : K-(w.toList.length+1) = (K-(w.toList.length+2))+1 := by omega
  simp only [fullSide,hk,List.replicate_succ',← List.append_assoc,List.getLast?_concat]

lemma sideFull_head (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+2 ≤ K) :
    (sideFull g s K).head? = some g := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,fullSide_head,fullSide_last _ _ _ h,mul_assoc]

lemma sideFull_last (g : TriangleGroup) (s : Side) (K : ℕ) (h : s.1.toList.length+2 ≤ K) :
    (sideFull g s K).getLast? = some (g*eval (sideWord s)) := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,sideWord,fullSide_head,fullSide_last _ _ _ h]

def startLabel (s : Fin 3 → Side) (i : Fin 3) : TriangleGroup :=
  if i = 0 then 1 else if i = 1 then eval (sideWord (s 0))
    else eval (sideWord (s 0))*eval (sideWord (s 1))

def closedSides (s : Fin 3 → Side) : Prop :=
  eval (sideWord (s 0))*eval (sideWord (s 1))*eval (sideWord (s 2)) = 1

lemma startLabel_next (s : Fin 3 → Side) (h : closedSides s) (i : Fin 3) :
    startLabel s i * eval (sideWord (s i)) = startLabel s (i+1) := by
  fin_cases i <;> simp [startLabel,show (2 : Fin 3) ≠ 1 by decide,closedSides] at *
  exact h

noncomputable def sideBoundary (s : Fin 3 → Side) (K : ℕ) : List TriangleGroup :=
  (sideFull (startLabel s 0) (s 0) K).dropLast ++
  (sideFull (startLabel s 1) (s 1) K).dropLast ++
  (sideFull (startLabel s 2) (s 2) K).dropLast

lemma sideBoundary_contract (s : Fin 3 → Side) (K : ℕ) (h : ∀ i, (s i).1.toList.length+2 ≤ K) :
    ReflTransGen PathStep (sideBoundary s K)
      (walk 1 (sideWord (s 0)*sideWord (s 1)*sideWord (s 2)).toList) := by
  let p (i : Fin 3) := (sideFull (startLabel s i) (s i) K).dropLast
  let q (i : Fin 3) := walk (startLabel s i) (sideWord (s i)).toList
  have hh i : ReflTransGen PathStep (p i) (q i) := sideFull_contract _ _ _ (h i)
  have h0 := deletions_context (hh 0) [] (p 1++p 2)
  have h1 := deletions_context (hh 1) (q 0) (p 2)
  have h2 := deletions_context (hh 2) (q 0++q 1) []
  have h3 := deletions_context (walk_join 1 (sideWord (s 0)).toList (sideWord (s 1)).toList)
    [] (q 2)
  have h4 := walk_join 1 (sideWord (s 0)*sideWord (s 1)).toList (sideWord (s 2)).toList
  have h01 := h0.trans (by simpa [List.append_assoc] using h1)
  have h012 := h01.trans (by simpa [List.append_assoc] using h2)
  have h0123 := h012.trans (by simpa [q,startLabel,List.append_assoc] using h3)
  simpa [sideBoundary,p,q,startLabel,List.append_assoc,mul_assoc] using h0123.trans
    (by simpa [q,startLabel,mul_assoc] using h4)

lemma sideBoundary_length (s : Fin 3 → Side) (K : ℕ) (h : ∀ i, (s i).1.toList.length+1 ≤ K) :
    (sideBoundary s K).length = 3*K := by
  simp only [sideBoundary,List.length_append,List.length_dropLast,sideFull_length _ _ _ (h _)]
  omega

lemma path_grid_pos {p q : List TriangleGroup} (h : PathHomotopy p q) (g : TriangleGroup) :
    ∃ B : ℕ, ∀ (N : ℕ) [NeZero N], B < N → GoodPath g p →
      ReflTransGen Strip (padded g p : Row N) (padded g q) := by
  obtain ⟨B,hB⟩ := path_grid h g
  refine ⟨B,?_⟩
  intro N hN hBN hp
  cases N with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ N => exact hB N (by omega) hp

/-- A finite collection of triangular loop types admits one common boundary
width and one common disk height. The boundary parametrizations reverse
literally, rather than merely up to homotopy. -/
theorem finite_template_fillers {I : Type*} [Fintype I] (s : I → Fin 3 → Side)
    (hs : ∀ i, closedSides (s i)) :
    ∃ K H : ℕ, ∃ hK : 0 < K, letI : NeZero (3*K) := ⟨by omega⟩;
      (∀ i j, (s i j).1.toList.length+2 ≤ K) ∧
      ∃ v : I → GridDisk.Vertex H (3*K) → TriangleGroup,
      (∀ i j, v i (Sum.inl (Fin.last (H+1),j)) = (sideBoundary (s i) K).getD j.val 1) ∧
      (∀ i a, ∃ t : TargetTriangle, ∀ k, ∃ j,
        t.vertex j = v i ((GridDisk.patch H (3*K)).tail (a,k))) := by
  classical
  have hW i : eval (sideWord (s i 0)*sideWord (s i 1)*sideWord (s i 2)) = 1 := by
    simpa only [map_mul,closedSides] using hs i
  choose B hB using fun i => path_grid_pos (null_path _ (hW i) 1) 1
  let K := 1 + (Finset.univ.sup B) +
    (Finset.univ.sup fun i : I => Finset.univ.sup fun j : Fin 3 => (s i j).1.toList.length+2)
  have hK : 0 < K := by dsimp [K]; omega
  let : NeZero (3*K) := ⟨by omega⟩
  have hbound (i : I) (j : Fin 3) : (s i j).1.toList.length+2 ≤ K := by
    have h1 := Finset.le_sup (f := fun j : Fin 3 => (s i j).1.toList.length+2) (Finset.mem_univ j)
    have h2 := Finset.le_sup (f := fun i : I => Finset.univ.sup fun j : Fin 3 =>
      (s i j).1.toList.length+2) (Finset.mem_univ i)
    dsimp only [K]
    omega
  have hrow (i : I) : ReflTransGen Strip (padded 1 (sideBoundary (s i) K) : Row (3*K)) (fun _ => 1) := by
    have hlen := sideBoundary_length (s i) K (fun j => by have := hbound i j; omega)
    have hc := sideBoundary_contract (s i) K (hbound i)
    have hwgood := walk_good 1 _ (hW i)
    have hpGood := (homotopy_good (deletions_homotopy hc) 1).2 hwgood
    have hd := deletions_grid hc hpGood (by omega : (sideBoundary (s i) K).length ≤ 3*K)
    have hi := Finset.le_sup (f := B) (Finset.mem_univ i)
    have hb : B i < 3*K := by dsimp only [K]; omega
    have ht := hB i (3*K) hb hwgood
    rw [pad_singleton] at ht
    exact hd.trans ht
  choose L hL using fun i => fill_row_tall 1 (padded 1 (sideBoundary (s i) K)) (hrow i)
  let H := Finset.univ.sup L
  choose v hv using fun i => hL i H (Finset.le_sup (Finset.mem_univ i))
  exact ⟨K,H,hK,hbound,v,fun i => (hv i).1,fun i => (hv i).2⟩

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram

lemma getD_dropLast {α : Type*} (l : List α) (d : α) (n : ℕ) (h : n < l.length-1) :
    l.dropLast.getD n d = l.getD n d := by
  rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by omega)]
  simp

lemma sideBoundary_get_interior (s : Fin 3 → Side)
    (K : ℕ) [NeZero K] (h : ∀ i, (s i).1.toList.length+2 ≤ K)
    (i : Fin 3) (j : ℕ) (hj : j<K) :
    (sideBoundary s K).getD (i.val*K+j) 1 =
      (sideFull (startLabel s i) (s i) K).getD j 1 := by
  have hlen (i : Fin 3) : (sideFull (startLabel s i) (s i) K).length = K+1 :=
    sideFull_length _ _ _ (by have := h i; omega)
  have hdlen (i : Fin 3) : ((sideFull (startLabel s i) (s i) K).dropLast).length = K := by
    rw [List.length_dropLast,hlen]; omega
  fin_cases i
  · change (sideBoundary s K).getD (0*K+j) 1 = _
    simp only [zero_mul,zero_add]
    rw [sideBoundary,getD_append_formula,List.length_append,hdlen,hdlen,ite_eq_left (by omega),
      getD_append_formula,hdlen,ite_eq_left hj]
    exact getD_dropLast _ _ _ (by rw [hlen]; omega)
  · change (sideBoundary s K).getD (1*K+j) 1 = _
    simp only [one_mul]
    rw [sideBoundary,getD_append_formula,List.length_append,hdlen,hdlen,ite_eq_left (by omega),
      getD_append_formula,hdlen,ite_eq_right (by omega)]
    rw [show K+j-K=j by omega,getD_dropLast _ _ _ (by rw [hlen]; omega)]
    congr 4
  · change (sideBoundary s K).getD (2*K+j) 1 = _
    rw [sideBoundary,getD_append_formula,List.length_append,hdlen,hdlen,ite_eq_right (by omega)]
    rw [show 2*K+j-(K+K)=j by omega]
    exact getD_dropLast _ _ _ (by rw [hlen]; omega)

lemma sideBoundary_get (s : Fin 3 → Side) (hs : closedSides s)
    (K : ℕ) [NeZero K] (h : ∀ i, (s i).1.toList.length+2 ≤ K)
    (i : Fin 3) (j : Fin (K+1)) :
    (sideBoundary s K).getD (GridDisk.sideIndex K i j).val 1 =
      (sideFull (startLabel s i) (s i) K).getD j.val 1 := by
  have hlen (i : Fin 3) : (sideFull (startLabel s i) (s i) K).length = K+1 :=
    sideFull_length _ _ _ (by have := h i; omega)
  by_cases hj : j.val < K
  · have hm : i.val*K+j.val < 3*K := by
      have hi : i.val*K ≤ 2*K := Nat.mul_le_mul_right K (by omega)
      omega
    change (sideBoundary s K).getD ((i.val*K+j.val)%(3*K)) 1 = _
    rw [Nat.mod_eq_of_lt hm]
    exact sideBoundary_get_interior s K h i j.val hj
  · have he : j = Fin.last K := by apply Fin.ext; simp; omega
    subst j
    have hg i : (sideFull (startLabel s i) (s i) K).getD K 1 = startLabel s (i+1) := by
      rw [← startLabel_next s hs i]
      have hl := sideFull_last (startLabel s i) (s i) K (h i)
      rw [List.getLast?_eq_getElem?,hlen] at hl
      change ((sideFull (startLabel s i) (s i) K)[K]?).getD 1 = _
      simpa only [Nat.add_sub_cancel_right,Option.getD_some] using
        congrArg (fun t : Option TriangleGroup => t.getD 1) hl
    simp only [Fin.val_last,hg]
    have he : GridDisk.sideIndex K i (Fin.last K) = GridDisk.sideIndex K (i+1) 0 := by
      have he := GridDisk.sidePoint_ends (H:=0) K i
      exact congrArg Prod.snd (Sum.inl.inj he)
    rw [he]
    have hm : (i+1).val*K < 3*K := Nat.mul_lt_mul_of_pos_right (i+1).isLt (NeZero.pos K)
    change (sideBoundary s K).getD (((i+1).val*K+0)%(3*K)) 1 = _
    rw [Nat.add_zero,Nat.mod_eq_of_lt hm]
    have hi := sideBoundary_get_interior s K h (i+1) 0 (NeZero.pos K)
    simp only [Nat.add_zero] at hi
    rw [hi]
    rw [List.getD,← List.head?_eq_getElem?]
    simp only [sideFull_head _ _ _ (h _),Option.getD_some]

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram

lemma walk_translate (a g : TriangleGroup) (w : List Letter) :
    walk (a*g) w = (walk g w).map (a*·) := by
  induction w generalizing g with
  | nil => rfl
  | cons s w ih => simp only [walk,List.map_cons,mul_assoc,ih]

lemma fullSide_translate (a g : TriangleGroup) (w : Word) (K : ℕ) :
    fullSide (a*g) w K = (fullSide g w K).map (a*·) := by
  simp [fullSide,walk_translate,mul_assoc]

lemma sideFull_translate (a g : TriangleGroup) (s : Side) (K : ℕ) :
    sideFull (a*g) s K = (sideFull g s K).map (a*·) := by
  rcases s with ⟨w,b⟩
  cases b <;> simp [sideFull,fullSide_translate,mul_assoc,List.map_reverse]

lemma sideFull_getTranslate (a g : TriangleGroup) (s : Side) (K : ℕ)
    (h : s.1.toList.length+1 ≤ K) (j : Fin (K+1)) :
    (sideFull (a*g) s K).getD j.val 1 = a*(sideFull g s K).getD j.val 1 := by
  rw [sideFull_translate]
  have hl : j.val < (sideFull g s K).length := by rw [sideFull_length _ _ _ h]; exact j.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hl),List.getD_eq_getElem _ _ hl]
  simp

lemma sideFull_getReverse (g : TriangleGroup) (s : Side) (K : ℕ)
    (h : s.1.toList.length+1 ≤ K) (j : Fin (K+1)) :
    (sideFull (g*eval (sideWord s)) (sideFlip s) K).getD j.rev.val 1 =
      (sideFull g s K).getD j.val 1 := by
  rw [← sideFull_reverse,List.getD_reverse j.rev.val (by
    rw [sideFull_length _ _ _ h]; exact j.rev.isLt),sideFull_length _ _ _ h]
  congr 1
  simp only [Fin.val_rev]
  omega

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open TriangleMesh

lemma TargetLegal_translate (b : TriangleGroup) {v : Fin 3 → TriangleGroup}
    (h : ∃ t : TargetTriangle, ∀ k, ∃ j, t.vertex j = v k) :
    ∃ t : TargetTriangle, ∀ k, ∃ j, t.vertex j = b*v k := by
  obtain ⟨t,ht⟩ := h
  refine ⟨⟨b*t.base,t.block,t.rel⟩,?_⟩
  intro k
  obtain ⟨j,hj⟩ := ht k
  refine ⟨j,?_⟩
  simpa only [TargetTriangle.vertex,mul_assoc] using congrArg (b*·) hj

section Refinement
variable {I F V : Type*} (M : TriangleMesh F V)
  (s : I → Fin 3 → Side) (hs : ∀ i, closedSides (s i))
  (K H : ℕ) [NeZero K]
  (hK : ∀ i j, (s i j).1.toList.length+2 ≤ K)
  (v : I → GridDisk.Vertex H (3*K) → TriangleGroup)
  (hv : ∀ i j, v i (Sum.inl (Fin.last (H+1),j)) = (sideBoundary (s i) K).getD j.val 1)
  (τ : F → I) (b : F → TriangleGroup) (z : V → TriangleGroup)
  (hb : ∀ f i, b f * startLabel (s (τ f)) i = z (M.tail (f,i)))
  (hm : ∀ f i, s (τ (M.mate (f,i)).1) (M.mate (f,i)).2 = sideFlip (s (τ f) i))
include hs hK hv hb hm

lemma template_seam (f : F) (i : Fin 3) (j : Fin (K+1)) :
    b f * v (τ f) ((GridDisk.sides H K).point (i,j)) =
      b (M.mate (f,i)).1 * v (τ (M.mate (f,i)).1)
        ((GridDisk.sides H K).point ((M.mate (f,i)).2,j.rev)) := by
  change b f * v (τ f) (Sum.inl (Fin.last (H+1),GridDisk.sideIndex K i j)) =
    b (M.mate (f,i)).1 * v (τ (M.mate (f,i)).1)
      (Sum.inl (Fin.last (H+1),GridDisk.sideIndex K (M.mate (f,i)).2 j.rev))
  rw [hv,hv,sideBoundary_get _ (hs _) K (hK _),sideBoundary_get _ (hs _) K (hK _),
    ← sideFull_getTranslate _ _ _ K (by have := hK (τ f) i; omega),
    ← sideFull_getTranslate _ _ _ K (by have := hK (τ (M.mate (f,i)).1) (M.mate (f,i)).2; omega),
    hb,hb,hm,M.tail_mate]
  have he : z (M.tail (f,i+1)) = z (M.tail (f,i))*eval (sideWord (s (τ f) i)) := by
    rw [← hb f (i+1),← hb f i,mul_assoc,startLabel_next _ (hs _)]
  rw [he]
  exact (sideFull_getReverse _ _ K (by have := hK (τ f) i; omega) j).symm

noncomputable def refinedLabels :
    Replacement.Vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K) → TriangleGroup :=
  Quot.lift (fun p : F × GridDisk.Vertex H (3*K) => b p.1*v (τ p.1) p.2) (by
    intro u w huw
    obtain ⟨f,i,j,rfl,rfl⟩ := huw
    exact template_seam M s hs K H hK v hv τ b z hb hm f i j)

lemma refinedLabels_tail (f : F) (a : GridDisk.Face H (3*K)) (i : Fin 3) :
    refinedLabels M s hs K H hK v hv τ b z hb hm
      ((Replacement.mesh M (GridDisk.patch H (3*K)) (GridDisk.sides H K)).tail ((f,a),i)) =
      b f*v (τ f) ((GridDisk.patch H (3*K)).tail (a,i)) := rfl

lemma refinedLabels_legal
    (hl : ∀ i a, ∃ t : TargetTriangle, ∀ k, ∃ j,
      t.vertex j = v i ((GridDisk.patch H (3*K)).tail (a,k)))
    (f : F × GridDisk.Face H (3*K)) :
    ∃ t : TargetTriangle, ∀ k, ∃ j, t.vertex j =
      refinedLabels M s hs K H hK v hv τ b z hb hm
        ((Replacement.mesh M (GridDisk.patch H (3*K)) (GridDisk.sides H K)).tail (f,k)) := by
  exact TargetLegal_translate (b f.1) (hl (τ f.1) f.2)

end Refinement
end ArtinCAT0.WordDiagram

namespace ArtinCAT0

@[simp] lemma mirrorLinear_one : mirrorLinear 1 = 1 := by simp [mirrorLinear]
@[simp] lemma mirrorLinear_inv (g : TriangleGroup) : mirrorLinear g⁻¹ = (mirrorLinear g)⁻¹ := by
  simp [mirrorLinear]
@[simp] lemma mirrorLinear_zpow (g : TriangleGroup) (n : ℤ) :
    mirrorLinear (g^n) = mirrorLinear g ^ n := by
  exact map_zpow (SemidirectProduct.rightHom.comp mirrorRepresentation) g n

lemma mirrorVector_pure_mul {g : TriangleGroup} (hg : mirrorLinear g = 1)
    (h : TriangleGroup) (d : Mirror) :
    mirrorVector (g*h) d = mirrorVector g d + mirrorVector h d := by
  rw [mirrorVector_mul,hg]
  rfl

lemma mirrorVector_pure_pow {g : TriangleGroup} (hg : mirrorLinear g = 1)
    (n : ℕ) (d : Mirror) : mirrorVector (g^n) d = (n:ℝ)*mirrorVector g d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mirrorVector_pure_mul hg,ih]
    push_cast
    ring

lemma mirrorVector_pure_zpow {g : TriangleGroup} (hg : mirrorLinear g = 1)
    (n : ℤ) (d : Mirror) : mirrorVector (g^n) d = (n:ℝ)*mirrorVector g d := by
  cases n with
  | ofNat n => simpa using mirrorVector_pure_pow hg n d
  | negSucc n =>
    rw [zpow_negSucc,mirrorVector_inv]
    have hpow : mirrorLinear (g^(n+1)) = 1 := by
      have h := mirrorLinear_zpow g (n+1)
      norm_cast at h
      rw [h,hg,one_pow]
    rw [hpow]
    simp only [Equiv.Perm.one_apply,mirrorVector_pure_pow hg,Int.cast_negSucc]
    ring

noncomputable def mirrorPlane (g : TriangleGroup) : ℝ × ℝ :=
  ((mirrorVector g (sideMirror 0)-mirrorVector g (extraMirror 0))/2,
    mirrorVector g (extraMirror 0)/2)

@[simp] lemma mirrorPlane_one : mirrorPlane 1 = (0,0) := by simp [mirrorPlane]

lemma mirrorPlane_pure_mul {g : TriangleGroup} (hg : mirrorLinear g = 1) (h : TriangleGroup) :
    mirrorPlane (g*h) = ( (mirrorPlane g).1+(mirrorPlane h).1,
      (mirrorPlane g).2+(mirrorPlane h).2) := by
  ext <;> simp only [mirrorPlane,mirrorVector_pure_mul hg] <;> ring

lemma mirrorPlane_pure_zpow {g : TriangleGroup} (hg : mirrorLinear g = 1) (n : ℤ) :
    mirrorPlane (g^n) = ((n:ℝ)*(mirrorPlane g).1,(n:ℝ)*(mirrorPlane g).2) := by
  ext <;> simp only [mirrorPlane,mirrorVector_pure_zpow hg] <;> ring

lemma mirrorPlane_mul_bound (g h : TriangleGroup) {D : ℝ}
    (hh : ∀ d, |mirrorVector h d| ≤ D) :
    |(mirrorPlane (g*h)).1-(mirrorPlane g).1| ≤ D ∧
    |(mirrorPlane (g*h)).2-(mirrorPlane g).2| ≤ D := by
  have hd : 0 ≤ D := (abs_nonneg _).trans (hh (sideMirror 0))
  constructor
  · change |(mirrorVector (g*h) (sideMirror 0)-mirrorVector (g*h) (extraMirror 0))/2-
      (mirrorVector g (sideMirror 0)-mirrorVector g (extraMirror 0))/2| ≤ D
    rw [mirrorVector_mul,mirrorVector_mul]
    have he (a b c d : ℝ) : (a+b-(c+d))/2-(a-c)/2 = (b-d)/2 := by ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have h1 := hh ((mirrorLinear g).symm (sideMirror 0))
    have h2 := hh ((mirrorLinear g).symm (extraMirror 0))
    exact (abs_sub _ _).trans (by linarith)
  · change |mirrorVector (g*h) (extraMirror 0)/2-mirrorVector g (extraMirror 0)/2| ≤ D
    rw [mirrorVector_mul,add_div,add_sub_cancel_left,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    linarith [hh ((mirrorLinear g).symm (extraMirror 0))]

namespace SixSector

def planeRay (i : Fin 6) : ℝ × ℝ :=
  if i = 0 ∨ i = 5 then (1,0) else if i = 1 then (0,1) else (0,0)

lemma ray_rep_even (i : Fin 3) :
    mirrorRepresentation (triangleGen i^2) =
      ⟨Multiplicative.ofAdd (2 • mirrorBasis (sideMirror i)),1⟩ := by
  rw [map_pow,mirrorRepresentation_gen,mirrorGenerator_sq]

lemma ray_rep_odd (i : Fin 3) :
    mirrorRepresentation (triangleH i^3) =
      ⟨Multiplicative.ofAdd (2 • (mirrorBasis (sideMirror i)+mirrorBasis (extraMirror i)+
        mirrorBasis (sideMirror (i+1)))),1⟩ := by
  rw [triangleH,map_pow,map_mul,mirrorRepresentation_gen,mirrorRepresentation_gen,
    mirrorGenerator_center]

lemma ray_pure (i : Fin 6) : mirrorLinear (ray i) = 1 := by
  have he k : mirrorLinear (triangleGen k^2) = 1 := by
    unfold mirrorLinear; rw [ray_rep_even]
  have ho k : mirrorLinear (triangleH k^3) = 1 := by
    unfold mirrorLinear; rw [ray_rep_odd]
  fin_cases i
  · exact he 0
  · exact ho 0
  · exact he 1
  · exact ho 1
  · exact he 2
  · exact ho 2

lemma ray_plane (i : Fin 6) : mirrorPlane (ray i) = planeRay i := by
  have he (k : Fin 3) (d : Mirror) :
      mirrorVector (triangleGen k^2) d = 2*mirrorBasis (sideMirror k) d := by
    simp [mirrorVector,ray_rep_even,two_smul]
    ring
  have ho (k : Fin 3) (d : Mirror) :
      mirrorVector (triangleH k^3) d =
        2*(mirrorBasis (sideMirror k) d+mirrorBasis (extraMirror k) d+
          mirrorBasis (sideMirror (k+1)) d) := by
    simp [mirrorVector,ray_rep_odd,two_smul]
    ring
  fin_cases i <;> ext <;>
    simp [ray,mirrorPlane,planeRay,he,ho,mirrorBasis,sideMirror,extraMirror]

lemma lattice_plane (i : Fin 6) (L M : ℝ) (p : ℝ × ℝ) :
    mirrorPlane (SectorMetric.lattice (ray i) (ray (i+1)) L M p) =
      ((⌊p.1/L⌋:ℝ)*(planeRay i).1+(⌊p.2/M⌋:ℝ)*(planeRay (i+1)).1,
       (⌊p.1/L⌋:ℝ)*(planeRay i).2+(⌊p.2/M⌋:ℝ)*(planeRay (i+1)).2) := by
  have h : mirrorLinear (ray i ^ ⌊p.1/L⌋) = 1 := by rw [mirrorLinear_zpow,ray_pure,one_zpow]
  rw [SectorMetric.lattice,mirrorPlane_pure_mul h,
    mirrorPlane_pure_zpow (ray_pure i),mirrorPlane_pure_zpow (ray_pure (i+1)),
    ray_plane,ray_plane]

end SixSector
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

namespace ArtinCAT0.SixSector
open SectorMetric

variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

noncomputable def rayLength (y : X) (i : Fin 6) := stableLengthAt y (ray i)
noncomputable def chart (y : X) (i : Fin 6) (p : Point) : TriangleGroup :=
  lattice (ray i) (ray (i+1)) (rayLength y i) (rayLength y (i+1)) p
noncomputable def axis (y : X) (i : Fin 6) (R : ℝ) : TriangleGroup := (ray i)^⌊R/rayLength y i⌋
noncomputable def circle (y : X) (R : ℝ) (i : Fin 6) (t : ℝ) : TriangleGroup :=
  chart y i (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2)

omit [ProperSpace X] [Nonempty X] in
@[simp] lemma chart_zero (y : X) (i : Fin 6) : chart y i (0,0) = 1 := lattice_origin _ _ _ _
omit [ProperSpace X] [Nonempty X] in
@[simp] lemma chart_axis1 (y : X) (i : Fin 6) (R : ℝ) : chart y i (R,0) = axis y i R := by
  simp [chart,lattice,axis]
omit [ProperSpace X] [Nonempty X] in
@[simp] lemma chart_axis2 (y : X) (i : Fin 6) (R : ℝ) : chart y i (0,R) = axis y (i+1) R := by
  simp [chart,lattice,axis]

lemma cosine_abs (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) (i : Fin 6) :
    |cosine y i| ≤ 1 := abs_le.mpr ⟨by linarith [cosine_lower hG y hR i],cosine_le_one hG y hR i⟩

omit [ProperSpace X] [Nonempty X] in
lemma circle_zero (y : X) (R : ℝ) (i : Fin 6) : circle y R i 0 = axis y i R := by
  simp [circle]
lemma circle_one (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
    (R : ℝ) (i : Fin 6) : circle y R i 1 = axis y (i+1) R := by
  simp [circle,unit_one _ (cosine_abs hG y hR i)]

theorem chart_uniform (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) :
    ∃ C : ℝ, 0≤C ∧ ∀ i p q,
      |dist (chart y i p • y) (chart y i q • y)-‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C := by
  have hh i : ∃ C : ℝ, 0≤C ∧ ∀ p q : Point,
      |dist (chart y i p • y) (chart y i q • y)-‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C := by
    apply lattice_metric hG y (ray_length_pos hG y hR i) (ray_length_pos hG y hR (i+1))
      (ray_commute i) (cosine_abs hG y hR i)
    unfold cosine
    field_simp [ne_of_gt (ray_length_pos hG y hR i),ne_of_gt (ray_length_pos hG y hR (i+1))]
  choose C hC hh using hh
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro i p q
  exact (hh i p q).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

section Estimates
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C : ℝ} (hC : 0≤C)
  (hchart : ∀ i p q, |dist (chart y i p • y) (chart y i q • y)-
    ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C)
include hG hR hchart

lemma circle_radius {R : ℝ} (hR0 : 0≤R) (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    |dist y (circle y R i t • y)-R| ≤ C := by
  have h := hchart i (0,0) (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2)
  rw [chart_zero,one_smul] at h
  simp only [sub_zero] at h
  rw [vec_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0,
    unit_vec (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht,mul_one] at h
  exact h

lemma circle_lipschitz {R : ℝ} (hR0 : 0≤R) (i : Fin 6) {s t : ℝ}
    (hs : s∈Set.Icc 0 1) (ht : t∈Set.Icc 0 1) :
    dist (circle y R i s • y) (circle y R i t • y) ≤ 20*R*|s-t|+C := by
  have h := (abs_le.mp (hchart i (R*(unit (cosine y i) s).1,R*(unit (cosine y i) s).2)
    (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2))).2
  have hb := vec_bound (cosine y i) (cosine_abs hG y hR i)
    (R*(unit (cosine y i) t).1-R*(unit (cosine y i) s).1,
      R*(unit (cosine y i) t).2-R*(unit (cosine y i) s).2)
  have hu := unit_lipschitz (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht hs
  simp only [← mul_sub,abs_mul,abs_of_nonneg hR0] at hb
  rw [abs_sub_comm t s] at hu
  change dist (circle y R i s • y) (circle y R i t • y)-_ ≤ C at h
  simp only [← mul_sub] at h
  nlinarith [mul_le_mul_of_nonneg_left hu.1 hR0,mul_le_mul_of_nonneg_left hu.2 hR0]

lemma axis_radius {R : ℝ} (hR0 : 0≤R) (i : Fin 6) :
    |dist y (axis y i R • y)-R| ≤ C := by
  simpa only [circle_zero] using circle_radius hG y hR hchart hR0 i (by norm_num : (0:ℝ)∈Set.Icc 0 1)

lemma circle_axis_chord {c r R : ℝ} (hc : ∀ i, c≤cosine y i) (hr : 0≤r) (hR0 : 0≤R)
    (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    dist (axis y i (r*R) • y) (circle y R i t • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C ∧
    dist (axis y (i+1) (r*R) • y) (circle y R i t • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C := by
  have hca := (cosine_lower hG y hR i).le
  have hcb := cosine_le_one hG y hR i
  have h1 := chord_axis1 hca hcb ht hr
  have h2 := chord_axis2 hca hcb ht hr
  have hd : 1+r^2-2*cosine y i*r ≤ 1+r^2-2*c*r := by nlinarith [hc i]
  have hn1 : ‖vec (cosine y i) ((unit (cosine y i) t).1-r,(unit (cosine y i) t).2)‖ ≤
      Real.sqrt (1+r^2-2*c*r) := by
    exact (Real.le_sqrt (norm_nonneg _) (by linarith [sq_nonneg ‖vec (cosine y i) ((unit (cosine y i) t).1-r,(unit (cosine y i) t).2)‖])).mpr (h1.trans hd)
  have hn2 : ‖vec (cosine y i) ((unit (cosine y i) t).1,(unit (cosine y i) t).2-r)‖ ≤
      Real.sqrt (1+r^2-2*c*r) := by
    exact (Real.le_sqrt (norm_nonneg _) (by linarith [sq_nonneg ‖vec (cosine y i) ((unit (cosine y i) t).1,(unit (cosine y i) t).2-r)‖])).mpr (h2.trans hd)
  constructor
  · have h := (abs_le.mp (hchart i (r*R,0) (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2))).2
    rw [chart_axis1] at h
    change dist (axis y i (r*R) • y) (circle y R i t • y)-_ ≤ C at h
    rw [show R*(unit (cosine y i) t).1-r*R = R*((unit (cosine y i) t).1-r) by ring,
      sub_zero,vec_mul (cosine y i) R ((unit (cosine y i) t).1-r,(unit (cosine y i) t).2),norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0] at h
    nlinarith [mul_le_mul_of_nonneg_left hn1 hR0]
  · have h := (abs_le.mp (hchart i (0,r*R) (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2))).2
    rw [chart_axis2] at h
    change dist (axis y (i+1) (r*R) • y) (circle y R i t • y)-_ ≤ C at h
    rw [show R*(unit (cosine y i) t).2-r*R = R*((unit (cosine y i) t).2-r) by ring,
      sub_zero,vec_mul (cosine y i) R ((unit (cosine y i) t).1,(unit (cosine y i) t).2-r),norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0] at h
    nlinarith [mul_le_mul_of_nonneg_left hn2 hR0]

lemma axis_adjacent {R : ℝ} (hR0 : 0≤R) (i : Fin 6) :
    dist (axis y i R • y) (axis y (i+1) R • y) ≤ R+C := by
  have h := (abs_le.mp (hchart i (R,0) (0,R))).2
  rw [chart_axis1,chart_axis2] at h
  have hs := vec_sq (cosine y i) (cosine_abs hG y hR i) (0-R,R-0)
  have hl := cosine_lower hG y hR i
  have hn : ‖vec (cosine y i) (0-R,R-0)‖ ≤ R := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl.le) (sq_nonneg R),norm_nonneg (vec (cosine y i) (0-R,R-0))]
  linarith

end Estimates
end ArtinCAT0.SixSector

namespace ArtinCAT0.SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

lemma common_cosine (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y) :
    ∃ c : ℝ, 1/2<c ∧ c≤1 ∧ ∀ i, c≤cosine y i := by
  classical
  let c := Finset.univ.inf' Finset.univ_nonempty (cosine y)
  refine ⟨c,?_,?_,?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun i _ => cosine_lower hG y hR i)
  · exact (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 6))).trans (cosine_le_one hG y hR 0)
  · intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)

lemma circle_detour (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
    {C : ℝ} (hC : 0≤C)
    (hchart : ∀ i p q, |dist (chart y i p • y) (chart y i q • y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C)
    {c r R : ℝ} (hc : ∀ i, c≤cosine y i) (hr : 0≤r) (hR0 : 0≤R)
    (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    dist (axis y 0 R • y) (circle y R i t • y) ≤
      (2*Real.sqrt (1+r^2-2*c*r)+r)*R+3*C := by
  have hleft : dist (axis y 0 R • y) (axis y 1 (r*R) • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C := by
    have h := (circle_axis_chord hG y hR hchart hc hr hR0 0 (by norm_num : (0:ℝ)∈Set.Icc 0 1)).2
    simpa only [circle_zero,Fin.reduceAdd,dist_comm] using h
  have hright : dist (axis y 0 R • y) (axis y 5 (r*R) • y) ≤ R*Real.sqrt (1+r^2-2*c*r)+C := by
    have h := (circle_axis_chord hG y hR hchart hc hr hR0 5 (by norm_num : (1:ℝ)∈Set.Icc 0 1)).1
    simpa only [circle_one hG y hR,Fin.reduceAdd,dist_comm] using h
  have h12 := axis_adjacent hG y hR hchart (mul_nonneg hr hR0) 1
  have h45 := axis_adjacent hG y hR hchart (mul_nonneg hr hR0) 4
  have hi := circle_axis_chord hG y hR hchart hc hr hR0 i ht
  rcases hi with ⟨hia,hib⟩
  fin_cases i
  · change dist (axis y 0 R • y) (circle y R 0 t • y) ≤ _
    change dist (axis y 0 (r*R) • y) (circle y R 0 t • y) ≤ _ at hia
    change dist (axis y 1 (r*R) • y) (circle y R 0 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 1 (r*R) • y) (circle y R 0 t • y)
    nlinarith [mul_nonneg hr hR0]
  · change dist (axis y 0 R • y) (circle y R 1 t • y) ≤ _
    change dist (axis y 1 (r*R) • y) (circle y R 1 t • y) ≤ _ at hia
    change dist (axis y 2 (r*R) • y) (circle y R 1 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 1 (r*R) • y) (circle y R 1 t • y)
    nlinarith [mul_nonneg hr hR0]
  · change dist (axis y 0 R • y) (circle y R 2 t • y) ≤ _
    change dist (axis y 2 (r*R) • y) (circle y R 2 t • y) ≤ _ at hia
    change dist (axis y 3 (r*R) • y) (circle y R 2 t • y) ≤ _ at hib
    have hh := dist_triangle4 (axis y 0 R • y) (axis y 1 (r*R) • y) (axis y 2 (r*R) • y) (circle y R 2 t • y)
    change dist (axis y 1 (r*R) • y) (axis y 2 (r*R) • y) ≤ r*R+C at h12
    nlinarith
  · change dist (axis y 0 R • y) (circle y R 3 t • y) ≤ _
    change dist (axis y 3 (r*R) • y) (circle y R 3 t • y) ≤ _ at hia
    change dist (axis y 4 (r*R) • y) (circle y R 3 t • y) ≤ _ at hib
    have hh := dist_triangle4 (axis y 0 R • y) (axis y 5 (r*R) • y) (axis y 4 (r*R) • y) (circle y R 3 t • y)
    change dist (axis y 4 (r*R) • y) (axis y 5 (r*R) • y) ≤ r*R+C at h45
    rw [dist_comm (axis y 4 (r*R) • y)] at h45
    nlinarith
  · change dist (axis y 0 R • y) (circle y R 4 t • y) ≤ _
    change dist (axis y 4 (r*R) • y) (circle y R 4 t • y) ≤ _ at hia
    change dist (axis y 5 (r*R) • y) (circle y R 4 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 5 (r*R) • y) (circle y R 4 t • y)
    nlinarith [mul_nonneg hr hR0]
  · change dist (axis y 0 R • y) (circle y R 5 t • y) ≤ _
    change dist (axis y 5 (r*R) • y) (circle y R 5 t • y) ≤ _ at hia
    change dist (axis y 0 (r*R) • y) (circle y R 5 t • y) ≤ _ at hib
    have hh := dist_triangle (axis y 0 R • y) (axis y 5 (r*R) • y) (circle y R 5 t • y)
    nlinarith [mul_nonneg hr hR0]

end ArtinCAT0.SixSector

namespace ArtinCAT0.WordDiagram

lemma eval_surjective : Function.Surjective eval := by
  let H : Subgroup TriangleGroup :=
    { carrier := Set.range eval
      one_mem' := ⟨1,map_one eval⟩
      mul_mem' := by rintro a b ⟨u,rfl⟩ ⟨v,rfl⟩; exact ⟨u*v,map_mul eval u v⟩
      inv_mem' := by rintro a ⟨u,rfl⟩; exact ⟨inverseWord u,eval_inverseWord u⟩ }
  have hh (i : Fin 3) : (PresentedGroup.of i : TriangleGroup) ∈ H := by
    refine ⟨positive i,?_⟩
    simp [positive,eval,signed,triangleGen]
  intro g
  exact PresentedGroup.generated_by triangleRelators H hh g

noncomputable def representative (g : TriangleGroup) : Word := (eval_surjective g).choose
@[simp] lemma eval_representative (g : TriangleGroup) : eval (representative g) = g :=
  (eval_surjective g).choose_spec

section FiniteLibrary
variable {E : Type*} [Fintype E] (e : E → TriangleGroup)

abbrev SmallSide := E × Bool
noncomputable def smallSide (s : SmallSide (E:=E)) : Side := (representative (e s.1),s.2)
def smallFlip (s : SmallSide (E:=E)) : SmallSide (E:=E) := (s.1,!s.2)

omit [Fintype E] in
@[simp] lemma smallSide_flip (s : SmallSide (E:=E)) :
    smallSide e (smallFlip s) = sideFlip (smallSide e s) := rfl

abbrev SmallLoop := {s : Fin 3 → SmallSide (E:=E) // closedSides (smallSide e ∘ s)}

noncomputable instance : Fintype (SmallLoop e) := Fintype.ofFinite _

noncomputable def loopSides (s : SmallLoop e) : Fin 3 → Side := smallSide e ∘ s.val
omit [Fintype E] in
lemma loops_closed (s : SmallLoop e) : closedSides (loopSides e s) := s.property

end FiniteLibrary

section Controlled
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X]

lemma finite_short_elements (hG : GeometricAction TriangleGroup X) (y : X)
    (B : ℝ) (hB : 0≤B) : {g : TriangleGroup | dist y (g•y) ≤ B}.Finite := by
  have h := finite_movers_of_compact hG.2.2.1 (isCompact_singleton : IsCompact ({y}:Set X)) y B hB
  simpa using h

variable (hG : GeometricAction TriangleGroup X) (y : X) (B : ℝ) (hB : 0≤B)
abbrev ShortElement := {g : TriangleGroup // dist y (g•y) ≤ B}
@[instance_reducible] noncomputable def shortElementFintype : Fintype (ShortElement y B) :=
  (finite_short_elements hG y B hB).fintype

omit [ProperSpace X] in
include hG in
lemma action_displacement (g h : TriangleGroup) :
    dist y ((g⁻¹*h)•y) = dist (g•y) (h•y) := (action_dist hG.2.1 y g h).symm

section Orient
variable {F V : Type*} [Fintype F] (M : TriangleMesh F V) (z : V → TriangleGroup)
  (hz : ∀ f i, dist (z (M.tail (f,i))•y) (z (M.tail (f,i+1))•y) ≤ B)

noncomputable def chooseForward (d : F × Fin 3) : Bool := by
  classical
  exact decide (Fintype.equivFin (F × Fin 3) d < Fintype.equivFin (F × Fin 3) (M.mate d))

lemma chooseForward_mate (d : F × Fin 3) : chooseForward M (M.mate d) = !chooseForward M d := by
  classical
  simp only [chooseForward,M.mate_involutive d]
  have hn : Fintype.equivFin (F × Fin 3) d ≠ Fintype.equivFin (F × Fin 3) (M.mate d) :=
    fun h => (M.mate_ne d).symm ((Fintype.equivFin _).injective h)
  by_cases h : Fintype.equivFin (F × Fin 3) d < Fintype.equivFin (F × Fin 3) (M.mate d)
  · simp [h,not_lt.mpr h.le]
  · have h' := lt_of_le_of_ne (le_of_not_gt h) hn.symm
    simp [h,h']

noncomputable def orientedSide (d : F × Fin 3) : ShortElement y B × Bool :=
  if chooseForward M d then
    (⟨(z (M.tail d))⁻¹*z (M.tail (d.1,d.2+1)),by rw [action_displacement hG y]; exact hz _ _⟩,false)
  else
    (⟨(z (M.tail (d.1,d.2+1)))⁻¹*z (M.tail d),by
      rw [action_displacement hG y,dist_comm]; exact hz _ _⟩,true)

omit [ProperSpace X] in
lemma orientedSide_mate (d : F × Fin 3) :
    orientedSide hG y B M z hz (M.mate d) = smallFlip (orientedSide hG y B M z hz d) := by
  classical
  unfold orientedSide
  rw [chooseForward_mate]
  have ht := M.tail_mate d
  have hh := M.tail_rotate_mate d
  change M.tail ((M.mate d).1,(M.mate d).2+1) = M.tail d at hh
  cases h : chooseForward M d <;> simp [smallFlip,ht,hh]

omit [ProperSpace X] in
lemma orientedSide_value (d : F × Fin 3) :
    eval (sideWord (smallSide (Subtype.val : ShortElement y B → TriangleGroup)
      (orientedSide hG y B M z hz d))) = (z (M.tail d))⁻¹*z (M.tail (d.1,d.2+1)) := by
  classical
  unfold orientedSide
  cases h : chooseForward M d <;> simp [smallSide,sideWord,mul_inv_rev]

noncomputable def faceLoop (f : F) : SmallLoop (Subtype.val : ShortElement y B → TriangleGroup) := by
  refine ⟨fun i => orientedSide hG y B M z hz (f,i),?_⟩
  change eval (sideWord (smallSide _ _))*eval (sideWord (smallSide _ _))*eval (sideWord (smallSide _ _)) = 1
  simp only [orientedSide_value]
  change (z (M.tail (f,0)))⁻¹*z (M.tail (f,1))*
    ((z (M.tail (f,1)))⁻¹*z (M.tail (f,2)))*
    ((z (M.tail (f,2)))⁻¹*z (M.tail (f,0))) = 1
  group

omit [ProperSpace X] in
lemma faceLoop_start (f : F) (i : Fin 3) :
    z (M.tail (f,0))*startLabel (loopSides _ (faceLoop hG y B M z hz f)) i = z (M.tail (f,i)) := by
  fin_cases i <;> simp [startLabel,loopSides,faceLoop,orientedSide_value,
    show (2:Fin 3)≠1 by decide,mul_assoc]

omit [ProperSpace X] in
lemma faceLoop_mate (f : F) (i : Fin 3) :
    loopSides _ (faceLoop hG y B M z hz (M.mate (f,i)).1) (M.mate (f,i)).2 =
      sideFlip (loopSides _ (faceLoop hG y B M z hz f) i) := by
  change smallSide _ (orientedSide hG y B M z hz (M.mate (f,i))) = _
  rw [orientedSide_mate,smallSide_flip]
  rfl

end Orient
end Controlled
end ArtinCAT0.WordDiagram

namespace ArtinCAT0.WordDiagram
open TriangleMesh

variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X]

/-- The constants are chosen before the mesh: refinement has uniformly bounded
metric displacement and uniformly bounded error in every mirror coordinate. -/
theorem controlled_refinement (hG : GeometricAction TriangleGroup X) (y : X)
    (B : ℝ) (hB : 0≤B) :
    ∃ K H : ℕ, ∃ hK : 0<K, letI : NeZero K := ⟨by omega⟩;
      ∃ C D : ℝ, 0≤C ∧ 0≤D ∧
      ∀ (F V : Type) [Fintype F] (M : TriangleMesh F V) (z : V → TriangleGroup),
      (∀ f i, dist (z (M.tail (f,i))•y) (z (M.tail (f,i+1))•y) ≤ B) →
      ∃ L : (Replacement.mesh M (GridDisk.patch H (3*K)) (GridDisk.sides H K)).SimplicialLabeling,
        (∀ f p,
          dist (L.vertex (Replacement.vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K) (f,p)) • y)
            (z (M.tail (f,0))•y) ≤ C) ∧
        (∀ f p d,
          |mirrorVector (L.vertex (Replacement.vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K) (f,p))) d-
            mirrorVector (z (M.tail (f,0))) d| ≤ D) ∧
        (∀ f i, L.vertex (Replacement.vertex M (GridDisk.patch H (3*K)) (GridDisk.sides H K)
            (f,(GridDisk.sides H K).point (i,0))) = z (M.tail (f,i))) := by
  classical
  let E := ShortElement y B
  let : Fintype E := shortElementFintype hG y B hB
  let e : E → TriangleGroup := Subtype.val
  let I := SmallLoop e
  let s := loopSides e
  obtain ⟨K,H,hK,hbound,v,hv,hl⟩ := finite_template_fillers s (loops_closed e)
  let : NeZero K := ⟨by omega⟩
  choose D hD hd using fun i p => mirrorVector_bounded (v i p)
  let C₀ : ℝ := ∑ i, ∑ p, dist y (v i p • y)
  let D₀ : ℝ := ∑ i, ∑ p, D i p
  have hC₀ : 0≤C₀ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  have hD₀ : 0≤D₀ := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun p _ => hD i p))
  have hc (i : I) (p : GridDisk.Vertex H (3*K)) : dist y (v i p • y) ≤ C₀ := by
    have h₁ : dist y (v i p • y) ≤ ∑ q, dist y (v i q • y) :=
      Finset.single_le_sum (f:=fun q => dist y (v i q • y)) (fun _ _ => dist_nonneg) (Finset.mem_univ p)
    exact h₁.trans (Finset.single_le_sum (f:=fun j => ∑ q, dist y (v j q • y))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) (Finset.mem_univ i))
  have hd₀ (i : I) (p : GridDisk.Vertex H (3*K)) (d : Mirror) : |mirrorVector (v i p) d| ≤ D₀ := by
    exact (hd i p d).trans ((Finset.single_le_sum (fun q _ => hD i q) (Finset.mem_univ p)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun q _ => hD j q)) (Finset.mem_univ i)))
  refine ⟨K,H,hK,C₀,D₀,hC₀,hD₀,?_⟩
  intro F V _ M z hz
  let τ : F → I := faceLoop hG y B M z hz
  let b : F → TriangleGroup := fun f => z (M.tail (f,0))
  have hb : ∀ f i, b f * startLabel (s (τ f)) i = z (M.tail (f,i)) :=
    faceLoop_start hG y B M z hz
  have hm : ∀ f i, s (τ (M.mate (f,i)).1) (M.mate (f,i)).2 = sideFlip (s (τ f) i) :=
    faceLoop_mate hG y B M z hz
  let w := refinedLabels M s (loops_closed e) K H hbound v hv τ b z hb hm
  have hw := refinedLabels_legal M s (loops_closed e) K H hbound v hv τ b z hb hm hl
  let L := SimplicialLabeling.ofVertices _ w hw
  refine ⟨L,?_,?_,?_⟩
  · intro f p
    change dist ((b f*v (τ f) p)•y) (b f•y) ≤ C₀
    rw [mul_smul,(hG.2.1 (b f)).dist_eq,dist_comm]
    exact hc _ _
  · intro f p d
    change |mirrorVector (b f*v (τ f) p) d-mirrorVector (b f) d| ≤ D₀
    rw [mirrorVector_mul,add_sub_cancel_left]
    exact hd₀ _ _ _
  · intro f i
    change b f*v (τ f) ((GridDisk.sides H K).point (i,0)) = _
    change b f*v (τ f) (Sum.inl (Fin.last (H+1),GridDisk.sideIndex K i 0)) = _
    rw [hv,sideBoundary_get _ (loops_closed e _) K (hbound _)]
    have hh := sideFull_head (startLabel (s (τ f)) i) (s (τ f) i) K (hbound _ i)
    rw [List.getD,show (0 : Fin (K+1)).val = 0 from rfl,← List.head?_eq_getElem?,hh,Option.getD_some]
    exact hb f i

end ArtinCAT0.WordDiagram

namespace ArtinCAT0.SixSector
open SectorMetric

lemma product_next {N : ℕ} [NeZero N] (a : Fin 6) (j : Fin N) :
    finProdFinEquiv (a,j)+1 =
      if h : j.val+1<N then finProdFinEquiv (a,⟨j.val+1,h⟩)
      else finProdFinEquiv (a+1,0) := by
  have hN : 0<N := NeZero.pos N
  have h6 : 1<6*N := by omega
  split_ifs with h
  · apply Fin.ext
    change (j.val+N*a.val+1%(6*N))%(6*N) = j.val+1+N*a.val
    rw [Nat.mod_eq_of_lt h6]
    have hm := Nat.mul_le_mul_left N (show a.val≤5 by omega)
    have hb : j.val+N*a.val+1<6*N := by omega
    rw [Nat.mod_eq_of_lt hb]
    omega
  · have hj : j.val+1=N := by omega
    apply Fin.ext
    change (j.val+N*a.val+1%(6*N))%(6*N) = 0+N*((a.val+1)%6)
    rw [Nat.mod_eq_of_lt h6,zero_add]
    have he : j.val+N*a.val+1 = (a.val+1)*N := by nlinarith
    rw [he]
    by_cases ha : a.val+1<6
    · rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right ha hN)]
      exact Nat.mul_comm _ _
    · have ha' : a.val=5 := by omega
      simp [ha',Nat.mul_comm]

variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

noncomputable def ringCircle (y : X) (N : ℕ) [NeZero N] (R : ℝ) (j : Fin (6*N)) : TriangleGroup :=
  let p := finProdFinEquiv.symm j
  circle y R p.1 (p.2.val/N)

lemma ringCircle_product (y : X) (N : ℕ) [NeZero N] (R : ℝ) (a : Fin 6) (j : Fin N) :
    ringCircle y N R (finProdFinEquiv (a,j)) = circle y R a (j.val/N) := by
  simp [ringCircle]

lemma angular_parameter {N : ℕ} [NeZero N] (j : Fin N) : (j.val/(N:ℝ)) ∈ Set.Icc 0 1 := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hN.le,(div_le_iff₀ hN).mpr (by rw [one_mul]; exact_mod_cast j.isLt.le)⟩

section Action
variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C : ℝ} (hchart : ∀ i p q, |dist (chart y i p • y) (chart y i q • y)-
    ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖| ≤ C)
include hG hR hchart

lemma ringCircle_radius (N : ℕ) [NeZero N] {R : ℝ} (hR0 : 0≤R) (j : Fin (6*N)) :
    |dist y (ringCircle y N R j •y)-R| ≤ C :=
  circle_radius hG y hR hchart hR0 _ (angular_parameter _)

lemma circle_radial (i : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1) (R S : ℝ) :
    dist (circle y R i t •y) (circle y S i t •y) ≤ |R-S|+C := by
  have h := (abs_le.mp (hchart i (R*(unit (cosine y i) t).1,R*(unit (cosine y i) t).2)
    (S*(unit (cosine y i) t).1,S*(unit (cosine y i) t).2))).2
  change dist (circle y R i t •y) (circle y S i t •y)-_ ≤ C at h
  simp only [← sub_mul] at h
  rw [vec_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    unit_vec (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht,mul_one,abs_sub_comm S R] at h
  linarith

lemma ringCircle_radial (N : ℕ) [NeZero N] (R S : ℝ) (j : Fin (6*N)) :
    dist (ringCircle y N R j •y) (ringCircle y N S j •y) ≤ |R-S|+C :=
  circle_radial hG y hR hchart _ (angular_parameter _) R S

lemma ringCircle_step (N : ℕ) [NeZero N] {R : ℝ} (hR0 : 0≤R) (j : Fin (6*N)) :
    dist (ringCircle y N R j •y) (ringCircle y N R (j+1) •y) ≤ 20*R/N+C := by
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  rw [product_next]
  split_ifs with h
  · rw [ringCircle_product,ringCircle_product]
    have hk : ((k.val+1:ℕ):ℝ)/N ∈ Set.Icc 0 1 := angular_parameter (⟨k.val+1,h⟩ : Fin N)
    have hh := circle_lipschitz hG y hR hchart hR0 a (angular_parameter k) hk
    have he : |(k.val:ℝ)/N-(k.val+1:ℕ)/N| = 1/N := by
      rw [abs_sub_comm]
      push_cast
      rw [← sub_div,add_sub_cancel_left,abs_div,abs_one,abs_of_pos hN]
    simpa only [he,mul_one_div] using hh
  · have hk : k.val+1=N := by omega
    rw [ringCircle_product,ringCircle_product]
    simp only [Fin.val_zero,Nat.cast_zero,zero_div,circle_zero]
    rw [← circle_one hG y hR R a]
    have hh := circle_lipschitz hG y hR hchart hR0 a (angular_parameter k)
      (by norm_num : (1:ℝ)∈Set.Icc 0 1)
    have he : |(k.val:ℝ)/N-1| = 1/N := by
      have hk' : (k.val:ℝ)+1=N := by exact_mod_cast hk
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (angular_parameter k).2)]
      apply (eq_div_iff hN.ne').mpr
      field_simp
      linarith
    simpa only [he,mul_one_div] using hh

end Action
end ArtinCAT0.SixSector

end OAI
end
end

section
section
namespace OAI

open scoped Classical

namespace ArtinCAT0.GridDisk
variable {H N : ℕ} [NeZero N]

lemma edges_bound {X : Type*} [PseudoMetricSpace X] (v : Vertex H N → X)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (ha : ∀ r i, dist (v (Sum.inl (r,i))) (v (Sum.inl (r,i+1))) ≤ A)
    (hb : ∀ (r : Fin (H+1)) i, dist (v (Sum.inl (r.succ,i))) (v (Sum.inl (r.castSucc,i))) ≤ B)
    (hc : ∀ i, dist (v (Sum.inl (0,i))) (v (Sum.inr ())) ≤ B) :
    ∀ f k, dist (v (tail H N (f,k))) (v (tail H N (f,k+1))) ≤ A+B := by
  have hdiag (r : Fin (H+1)) (i : Fin N) :
      dist (v (Sum.inl (r.succ,i))) (v (Sum.inl (r.castSucc,i+1))) ≤ A+B :=
    (dist_triangle _ (v (Sum.inl (r.succ,i+1))) _).trans (add_le_add (ha _ _) (hb _ _))
  rintro (⟨r,i,b⟩ | i) k
  · cases b <;> fin_cases k
    · exact (ha _ _).trans (by linarith)
    · exact (hb _ _).trans (by linarith)
    · change dist (v (Sum.inl (r.castSucc,i+1))) (v (Sum.inl (r.succ,i))) ≤ A+B
      rw [dist_comm]
      exact hdiag r i
    · exact hdiag r i
    · change dist (v (Sum.inl (r.castSucc,i+1))) (v (Sum.inl (r.castSucc,i))) ≤ A+B
      rw [dist_comm]
      exact (ha r.castSucc i).trans (by linarith)
    · change dist (v (Sum.inl (r.castSucc,i))) (v (Sum.inl (r.succ,i))) ≤ A+B
      rw [dist_comm]
      exact (hb r i).trans (by linarith)
  · fin_cases k
    · exact (ha _ _).trans (by linarith)
    · exact (hc _).trans (by linarith)
    · change dist (v (Sum.inr ())) (v (Sum.inl (0,i))) ≤ A+B
      rw [dist_comm]
      exact (hc i).trans (by linarith)

end ArtinCAT0.GridDisk

namespace ArtinCAT0.TrianglePatch
variable {A U : Type*} [Fintype A] (P : TrianglePatch A U)

lemma sum_faces_boundary (w : A × Fin 3 → ℤ)
    (ha : ∀ d, ¬P.Boundary d → w (P.mate d) = -w d) :
    (∑ a, ∑ i, w (a,i)) = ∑ d, if P.Boundary d then w d else 0 := by
  classical
  let interior (d : A × Fin 3) := if P.Boundary d then 0 else w d
  have hb (d) : P.Boundary (P.mate d) ↔ P.Boundary d := by
    change P.mate (P.mate d)=P.mate d ↔ P.mate d=d
    rw [P.mate_mate]
    exact eq_comm
  have hi (d) : interior (P.mate d) = -interior d := by
    by_cases hd : P.Boundary d <;> simp only [interior,hb,hd,ite_true,ite_false,neg_zero]
    exact ha d hd
  have hz : ∑ d, interior d = 0 := by
    have h := Equiv.sum_comp P.mate interior
    simp only [hi,Finset.sum_neg_distrib] at h
    omega
  rw [← Fintype.sum_prod_type]
  have he (d) : w d = interior d+(if P.Boundary d then w d else 0) := by
    by_cases hd : P.Boundary d <;> simp [interior,hd]
  have hh : (∑ d, w d) = (∑ d, interior d)+(∑ d, if P.Boundary d then w d else 0) := by
    conv_lhs => arg 2; intro d; rw [he d]
    exact Finset.sum_add_distrib
  rw [hh,hz,zero_add]

namespace Sides
variable {K : ℕ} [NeZero K] (S : P.Sides K)

noncomputable def boundaryEquiv : (Fin 3 × Fin K) ≃ {d : A × Fin 3 // P.Boundary d} :=
  Equiv.ofBijective (fun e => ⟨S.dart e,S.fixed e⟩) ⟨
    fun _ _ h => S.dart_injective (congrArg Subtype.val h),by
      rintro ⟨d,hd⟩
      obtain ⟨e,he⟩ := S.complete d hd
      exact ⟨e,Subtype.ext he⟩⟩

omit [NeZero K] in
lemma sum_boundary (w : A × Fin 3 → ℤ) :
    (∑ d, if P.Boundary d then w d else 0) = ∑ i : Fin 3, ∑ j : Fin K, w (S.dart (i,j)) := by
  classical
  rw [← Finset.sum_filter,← Fintype.sum_prod_type (fun d : Fin 3 × Fin K => w (S.dart d))]
  symm
  apply Finset.sum_bij (fun e _ => S.dart e)
  · intro e _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.fixed e⟩
  · intro e _ f _ hef
    exact S.dart_injective hef
  · intro d hd
    obtain ⟨e,he⟩ := S.complete d (Finset.mem_filter.mp hd).2
    exact ⟨e,Finset.mem_univ _,he⟩
  · intro e _
    rfl

end Sides
end ArtinCAT0.TrianglePatch

namespace ArtinCAT0.TriangleMesh
variable {F V : Type*} [Fintype F] (M : TriangleMesh F V)

lemma region_stokes (Q : F → Prop) [DecidablePred Q] (w : F × Fin 3 → ℤ)
    (hw : ∀ d, w (M.mate d) = -w d) :
    (∑ f, if Q f then ∑ i, w (f,i) else 0) =
      ∑ d, if Q d.1 ∧ ¬Q (M.mate d).1 then w d else 0 := by
  classical
  let interior (d : F × Fin 3) := if Q d.1 ∧ Q (M.mate d).1 then w d else 0
  have ha (d) : interior (M.mate d) = -interior d := by
    dsimp only [interior]
    rw [M.mate_mate]
    by_cases hf : Q d.1 <;> by_cases hg : Q (M.mate d).1 <;>
      simp only [hf,hg,and_self,and_true,and_false,ite_true,ite_false,neg_zero]
    exact hw d
  have hz : ∑ d, interior d = 0 := by
    have he := Equiv.sum_comp M.mate interior
    simp only [ha,Finset.sum_neg_distrib] at he
    omega
  have he : (∑ f, if Q f then ∑ i, w (f,i) else 0) = ∑ d, if Q d.1 then w d else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : Q f <;> simp [hf]
  rw [he]
  have hd (d) : (if Q d.1 then w d else 0) =
      interior d+(if Q d.1 ∧ ¬Q (M.mate d).1 then w d else 0) := by
    by_cases hf : Q d.1 <;> by_cases hg : Q (M.mate d).1 <;> simp [hf,hg,interior]
  simp only [hd,Finset.sum_add_distrib,hz,zero_add]

namespace Replacement
open RayIndex
variable {A U : Type*} [Fintype A] (P : TrianglePatch A U) {K : ℕ} [NeZero K] (S : P.Sides K)

noncomputable def edgeFlux (p : Vertex M P S → RayIndex.Point) (f : F) (i : Fin 3) : ℤ :=
  ∑ j : Fin K, edge (p (vertex M P S (f,S.point (i,j.castSucc))))
    (p (vertex M P S (f,S.point (i,j.succ))))

omit [Fintype F] [Fintype A] [NeZero K] in
lemma point_seam (p : Vertex M P S → RayIndex.Point) (f : F) (i : Fin 3) (j : Fin (K+1)) :
    p (vertex M P S ((M.mate (f,i)).1,S.point ((M.mate (f,i)).2,j))) =
      p (vertex M P S (f,S.point (i,j.rev))) := by
  have h := vertex_seam M P S f i j.rev
  rw [Fin.rev_rev] at h
  exact congrArg p h.symm

omit [Fintype F] [Fintype A] [NeZero K] in
lemma edgeFlux_mate (p : Vertex M P S → RayIndex.Point) (d : F × Fin 3) :
    edgeFlux M P S p (M.mate d).1 (M.mate d).2 = -edgeFlux M P S p d.1 d.2 := by
  rcases d with ⟨f,i⟩
  unfold edgeFlux
  calc
    _ = ∑ j : Fin K, -edge (p (vertex M P S (f,S.point (i,j.rev.castSucc))))
        (p (vertex M P S (f,S.point (i,j.rev.succ)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [point_seam M P S p f i j.castSucc,point_seam M P S p f i j.succ,
        Fin.rev_castSucc,Fin.rev_succ,edge_reverse]
    _ = _ := by
      rw [Finset.sum_neg_distrib]
      congr 1
      exact Equiv.sum_comp Fin.revPerm (fun j : Fin K =>
        edge (p (vertex M P S (f,S.point (i,j.castSucc))))
          (p (vertex M P S (f,S.point (i,j.succ)))))

omit [Fintype F] in
lemma fiber_index (p : Vertex M P S → RayIndex.Point) (f : F) :
    (∑ a, face (fun i => p ((mesh M P S).tail ((f,a),i)))) =
      ∑ i, edgeFlux M P S p f i := by
  let q : U → RayIndex.Point := fun u => p (vertex M P S (f,u))
  let w (d : A × Fin 3) := edge (q (P.tail d)) (q (P.tail (d.1,d.2+1)))
  have ha (d) (hd : ¬P.Boundary d) : w (P.mate d) = -w d := by
    dsimp only [w]
    rw [P.tail_mate d hd,P.tail_rotate_mate d hd]
    exact edge_reverse _ _
  change (∑ a, ∑ i, w (a,i)) = _
  rw [P.sum_faces_boundary w ha,S.sum_boundary]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [w]
  rw [S.tail,S.head]

lemma region_index (Q : F → Prop) [DecidablePred Q]
    (p : Vertex M P S → RayIndex.Point) (q : V → RayIndex.Point)
    (hb : ∀ f i, Q f → ¬Q (M.mate (f,i)).1 →
      edgeFlux M P S p f i = edge (q (M.tail (f,i))) (q (M.tail (f,i+1)))) :
    (∑ f : F × A, if Q f.1 then face (fun i => p ((mesh M P S).tail (f,i))) else 0) =
      ∑ f, if Q f then face (fun i => q (M.tail (f,i))) else 0 := by
  rw [Fintype.sum_prod_type]
  have he (f) : (∑ a, if Q f then face (fun i => p ((mesh M P S).tail ((f,a),i))) else 0) =
      if Q f then ∑ i, edgeFlux M P S p f i else 0 := by
    by_cases hf : Q f
    · simp only [hf,ite_true,fiber_index]
    · simp only [hf,ite_false,Finset.sum_const_zero]
  simp only [he]
  rw [M.region_stokes Q (fun d => edgeFlux M P S p d.1 d.2) (edgeFlux_mate M P S p),
    RayIndex.patch_boundary_sum M Q q]
  apply Finset.sum_congr rfl
  rintro ⟨f,i⟩ _
  by_cases h : Q f ∧ ¬Q (M.mate (f,i)).1
  · simp only [h]
    exact hb f i h.1 h.2
  · simp only [h,ite_false]

end Replacement
end ArtinCAT0.TriangleMesh

namespace ArtinCAT0

section ConeMetric
variable {X : Type*} [MetricSpace X]

lemma segment_dist_start {a b : X} {γ : ℝ→X} (h : Segment a b γ)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : dist (γ t) a = t*dist a b := by
  have hh := h.2.2 t ht 0 (by norm_num)
  simpa only [h.1,sub_zero,abs_of_nonneg ht.1] using hh

lemma segment_dist_end {a b : X} {γ : ℝ→X} (h : Segment a b γ)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : dist (γ t) b = (1-t)*dist a b := by
  have hh := h.2.2 t ht 1 (by norm_num)
  simpa only [h.2.1,abs_sub_comm t 1,abs_of_nonneg (sub_nonneg.mpr ht.2)] using hh

lemma segment_radius_lower {a b y : X} {γ : ℝ→X} (h : Segment a b γ)
    {t A L : ℝ} (ht : t∈Set.Icc 0 1) (ha : A≤dist y a) (hb : A≤dist y b)
    (hL : dist a b≤L) : A-L/2≤dist y (γ t) := by
  have h1 := dist_triangle y (γ t) a
  have h2 := dist_triangle y (γ t) b
  rw [segment_dist_start h ht] at h1
  rw [segment_dist_end h ht] at h2
  nlinarith

end ConeMetric

namespace GridDisk
variable {H N : ℕ} [NeZero N]

noncomputable def rowTime (r : Fin (H+2)) : ℝ := r.val/(H+1:ℕ)

lemma rowTime_mem (r : Fin (H+2)) : rowTime r∈Set.Icc 0 1 := by
  have hp : (0:ℝ)<(H+1:ℕ) := Nat.cast_pos.mpr (by omega)
  refine ⟨div_nonneg (Nat.cast_nonneg _) hp.le,?_⟩
  apply (div_le_iff₀ hp).mpr
  rw [one_mul]
  exact_mod_cast (show r.val≤H+1 by omega)

@[simp] lemma rowTime_zero : rowTime (0 : Fin (H+2)) = 0 := by simp [rowTime]
@[simp] lemma rowTime_last : rowTime (Fin.last (H+1)) = 1 := by
  simp only [rowTime,Fin.val_last]
  exact div_self (Nat.cast_ne_zero.mpr (by omega))

lemma rowTime_step (r : Fin (H+1)) : |rowTime r.succ-rowTime r.castSucc| = 1/(H+1:ℕ) := by
  have hp : (0:ℝ)<(H+1:ℕ) := Nat.cast_pos.mpr (by omega)
  simp only [rowTime,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,← sub_div,add_sub_cancel_left]
  rw [abs_div,abs_one,abs_of_pos (by positivity : (0:ℝ)<(H:ℝ)+1)]

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
variable (y : X) (base : G) (boundary : Fin N → G) (γ : Fin N → ℝ → X) (round : X→G)

noncomputable def conePoint : Vertex H N → X
  | Sum.inl (r,i) => γ i (rowTime r)
  | Sum.inr _ => base •y

noncomputable def coneLabel : Vertex H N → G
  | Sum.inl (r,i) => if r=Fin.last (H+1) then boundary i else round (γ i (rowTime r))
  | Sum.inr _ => base

omit [NeZero N] [Group G] [MetricSpace X] [MulAction G X] in
@[simp] lemma coneLabel_outer (i : Fin N) :
    coneLabel base boundary γ round (Sum.inl (Fin.last (H+1),i)) = boundary i := by
  simp [coneLabel]

variable (hγ : ∀ i, Segment (base•y) (boundary i•y) (γ i))
  {E : ℝ} (hE : 0≤E) (hround : ∀ x, dist x (round x•y)≤E)

include hγ hE hround in
omit [NeZero N] in
lemma cone_approx (p : Vertex H N) :
    dist (conePoint y base γ p) (coneLabel base boundary γ round p•y)≤E := by
  rcases p with ⟨r,i⟩|u
  · by_cases hr : r=Fin.last (H+1)
    · subst r
      simp only [conePoint,rowTime_last,hγ i |>.2.1,coneLabel_outer,dist_self]
      exact hE
    · simpa only [conePoint,coneLabel,ite_eq_right hr] using hround (γ i (rowTime r))
  · simpa only [conePoint,coneLabel,dist_self] using hE

include hγ in
lemma conePoint_horizontal (hX : CAT0 X) {A : ℝ}
    (ha : ∀ i, dist (boundary i•y) (boundary (i+1)•y)≤A)
    (r : Fin (H+2)) (i : Fin N) :
    dist (conePoint y base γ (Sum.inl (r,i))) (conePoint y base γ (Sum.inl (r,i+1)))≤A := by
  have hh := comparison_common_start hX (hγ i) (hγ (i+1)) (rowTime_mem r)
  exact hh.trans ((mul_le_mul_of_nonneg_right (rowTime_mem r).2 dist_nonneg).trans (by simpa using ha i))

include hγ in
omit [NeZero N] in
lemma conePoint_radial {B : ℝ}
    (hb : ∀ i, dist (base•y) (boundary i•y)≤(H+1:ℕ)*B)
    (r : Fin (H+1)) (i : Fin N) :
    dist (conePoint y base γ (Sum.inl (r.succ,i))) (conePoint y base γ (Sum.inl (r.castSucc,i)))≤B := by
  change dist (γ i (rowTime r.succ)) (γ i (rowTime r.castSucc))≤B
  rw [(hγ i).2.2 _ (rowTime_mem _) _ (rowTime_mem _),rowTime_step,one_div_mul_eq_div]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0<H+1))).mpr (by simpa only [mul_comm] using hb i)

include hγ in
omit [NeZero N] in
lemma conePoint_center (i : Fin N) :
    conePoint y base γ (Sum.inl (0,i) : Vertex H N) = conePoint y base γ (Sum.inr () : Vertex H N) := by
  simp only [conePoint,rowTime_zero,(hγ i).1]

include hγ hE hround in
omit [NeZero N] in
lemma coneLabel_radius {A L : ℝ} (ha : A≤dist y (base•y))
    (hb : ∀ i, A≤dist y (boundary i•y)) (hL : ∀ i, dist (base•y) (boundary i•y)≤L)
    (hL0 : 0≤L) (p : Vertex H N) :
    A-L/2-E ≤ dist y (coneLabel base boundary γ round p•y) := by
  have hp : A-L/2≤dist y (conePoint y base γ p) := by
    rcases p with ⟨r,i⟩|u
    · exact segment_radius_lower (hγ i) (rowTime_mem r) ha (hb i) (hL i)
    · change A-L/2≤dist y (base•y)
      linarith
  have hq := cone_approx y base boundary γ round hγ hE hround p
  have hh := dist_triangle y (coneLabel base boundary γ round p•y) (conePoint y base γ p)
  rw [dist_comm (coneLabel base boundary γ round p•y)] at hh
  linarith

end GridDisk
end ArtinCAT0

open scoped Classical

namespace ArtinCAT0.GridDisk
variable (K : ℕ) [NeZero K]

lemma sideIndex_reverse (i : Fin 3) (j : Fin (K+1)) :
    sideIndex K (-i-1) j.rev = -sideIndex K i j := by
  have hK := NeZero.pos K
  have hj : j.val≤K := by omega
  fin_cases i
  · change sideIndex K 2 j.rev = -sideIndex K 0 j
    apply Fin.ext
    simp only [sideIndex,Fin.val_mk,Fin.val_rev,Fin.neg_def]
    change (2*K+(K+1-(j.val+1))) % (3*K) = (3*K-(0*K+j.val)%(3*K))%(3*K)
    rw [Nat.mod_eq_of_lt (show 0*K+j.val<3*K by omega)]
    congr 1
    omega
  · change sideIndex K 1 j.rev = -sideIndex K 1 j
    apply Fin.ext
    simp only [sideIndex,Fin.val_mk,Fin.val_rev,Fin.neg_def]
    change (1*K+(K+1-(j.val+1))) % (3*K) = (3*K-(1*K+j.val)%(3*K))%(3*K)
    rw [Nat.mod_eq_of_lt (show 1*K+j.val<3*K by omega)]
    congr 1
    omega
  · change sideIndex K 0 j.rev = -sideIndex K 2 j
    apply Fin.ext
    simp only [sideIndex,Fin.val_mk,Fin.val_rev,Fin.neg_def]
    change (0*K+(K+1-(j.val+1))) % (3*K) = (3*K-(2*K+j.val)%(3*K))%(3*K)
    by_cases h : j.val=K
    · simp [h,show 2*K+K=3*K by omega]
    · rw [Nat.mod_eq_of_lt (show 2*K+j.val<3*K by omega)]
      congr 1
      omega

end ArtinCAT0.GridDisk

namespace ArtinCAT0.GridSphere
open TriangleMesh
variable (H K : ℕ) [NeZero K]

abbrev Face := Bool × GridDisk.Face H (3*K)
abbrev Vertex := Replacement.Vertex doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K)
noncomputable def mesh : TriangleMesh (Face H K) (Vertex H K) :=
  Replacement.mesh doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K)

lemma exact : (mesh H K).Exact :=
  Replacement.exact doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K)
    doubleTriangle_exact (GridDisk.exact H (3*K))

variable {Z : Type*} (u v : GridDisk.Vertex H (3*K) → Z)
  (hv : ∀ i, u (Sum.inl (Fin.last (H+1),i)) = v (Sum.inl (Fin.last (H+1),-i)))

noncomputable def label : Vertex H K → Z := Quot.lift
  (fun p => if p.1 then v p.2 else u p.2) (by
    rintro _ _ ⟨b,i,j,rfl,rfl⟩
    change (if b then v (GridDisk.sidePoint H K (i,j)) else u (GridDisk.sidePoint H K (i,j))) =
      (if !b then v (GridDisk.sidePoint H K (-i-1,j.rev)) else u (GridDisk.sidePoint H K (-i-1,j.rev)))
    simp only [GridDisk.sidePoint,GridDisk.sideIndex_reverse]
    cases b
    · exact hv _
    · simpa only [Bool.not_true,Bool.false_eq_true,ite_true,ite_false,neg_neg] using (hv (-GridDisk.sideIndex K i j)).symm)

@[simp] lemma label_vertex (b : Bool) (p : GridDisk.Vertex H (3*K)) :
    label H K u v hv (Replacement.vertex doubleTriangle (GridDisk.patch H (3*K)) (GridDisk.sides H K) (b,p)) =
      if b then v p else u p := rfl

@[simp] lemma label_tail (b : Bool) (f : GridDisk.Face H (3*K)) (i : Fin 3) :
    label H K u v hv ((mesh H K).tail ((b,f),i)) =
      if b then v (GridDisk.tail H (3*K) (f,i)) else u (GridDisk.tail H (3*K) (f,i)) := rfl

lemma edges {X : Type*} [PseudoMetricSpace X] (a : Z → X) {B : ℝ}
    (hu : ∀ f i, dist (a (u (GridDisk.tail H (3*K) (f,i))))
      (a (u (GridDisk.tail H (3*K) (f,i+1))))≤B)
    (hv' : ∀ f i, dist (a (v (GridDisk.tail H (3*K) (f,i))))
      (a (v (GridDisk.tail H (3*K) (f,i+1))))≤B) :
    ∀ f i, dist (a (label H K u v hv ((mesh H K).tail (f,i))))
      (a (label H K u v hv ((mesh H K).tail (f,i+1))))≤B := by
  rintro ⟨b,f⟩ i
  cases b
  · exact hu f i
  · exact hv' f i

lemma frontier (f : Face H K) (i : Fin 3) :
    (f.1=false ∧ ((mesh H K).mate (f,i)).1.1 ≠ false) ↔
      f.1=false ∧ (GridDisk.patch H (3*K)).Boundary (f.2,i) := by
  rcases f with ⟨b,f⟩
  change (b=false ∧ (Replacement.mateFun doubleTriangle (GridDisk.patch H (3*K))
    (GridDisk.sides H K) ((b,f),i)).1.1≠false) ↔ _
  by_cases h : (GridDisk.patch H (3*K)).Boundary (f,i)
  · cases b <;> simp [Replacement.mateFun,h,doubleTriangle]
  · cases b <;> simp [Replacement.mateFun,h]

omit [NeZero K] in

lemma inner_sum (w : Face H K → ℤ) :
    (∑ f, if f.1=false then w f else 0) = ∑ f, w (false,f) := by
  rw [Fintype.sum_prod_type]
  simp

end ArtinCAT0.GridSphere

open scoped Classical
namespace ArtinCAT0.RayIndex

lemma det_pos_diagonal {p q : Point} (hp : 0<p.1+p.2) (hq : 0<q.1+q.2)
    (hy : p.2≤0) (hy' : 0<q.2) : 0<det p q := by
  have h1 := mul_pos hp hy'
  have h2 := mul_nonpos_of_nonneg_of_nonpos hq.le hy
  dsimp only [det]
  nlinarith

lemma edge_diagonal {p q : Point} (hp : 0<p.1+p.2) (hq : 0<q.1+q.2) :
    edge p q = above q-above p := by
  by_cases hy : p.2≤0 <;> by_cases hy' : q.2≤0
  · simp [edge,upward,above,not_lt.mpr hy,not_lt.mpr hy']
  · have hq' := lt_of_not_ge hy'
    have hd := det_pos_diagonal hp hq hy hq'
    simp [edge,upward,above,hy,hy',not_lt.mpr hy,hq',hd]
  · have hp' := lt_of_not_ge hy
    have hd := det_pos_diagonal hq hp hy' hp'
    simp [edge,upward,above,hy,hy',not_lt.mpr hy',hp',hd]
  · simp [edge,upward,above,hy,hy',lt_of_not_ge hy,lt_of_not_ge hy']

lemma sum_chain {K : ℕ} (p : Fin (K+1) → ℤ) :
    (∑ j : Fin K, (p j.succ-p j.castSucc)) = p (Fin.last K)-p 0 := by
  have h1 := Fin.sum_univ_succ p
  have h2 := Fin.sum_univ_castSucc p
  rw [Finset.sum_sub_distrib]
  omega

lemma edge_chain_diagonal {K : ℕ} (p : Fin (K+1) → Point)
    (hp : ∀ i, 0<(p i).1+(p i).2) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = above (p (Fin.last K))-above (p 0) := by
  simp_rw [edge_diagonal (hp _) (hp _)]
  exact sum_chain (fun i => above (p i))

lemma edge_chain_left {K : ℕ} (p : Fin (K+1) → Point) (hp : ∀ i, (p i).1<0) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = 0 := by
  simp [edge_left (hp _) (hp _)]

lemma edge_chain_low {K : ℕ} (p : Fin (K+1) → Point) (hp : ∀ i, (p i).2≤0) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = 0 := by
  simp [edge_low (hp _) (hp _)]

end ArtinCAT0.RayIndex

open scoped Classical
namespace ArtinCAT0

lemma mirrorPlane_close {g h : TriangleGroup} {D : ℝ}
    (hh : ∀ d, |mirrorVector g d-mirrorVector h d|≤D) :
    |(mirrorPlane g).1-(mirrorPlane h).1|≤D ∧
      |(mirrorPlane g).2-(mirrorPlane h).2|≤D := by
  have hd : 0≤D := (abs_nonneg _).trans (hh (sideMirror 0))
  have h1 := hh (sideMirror 0)
  have h2 := hh (extraMirror 0)
  simp only [mirrorPlane] at *
  rcases abs_le.mp h1 with ⟨h1a,h1b⟩
  rcases abs_le.mp h2 with ⟨h2a,h2b⟩
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

namespace SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

lemma chart_plane_first (y : X) (p : Point) :
    mirrorPlane (chart y 0 p) = ((⌊p.1/rayLength y 0⌋:ℝ),(⌊p.2/rayLength y 1⌋:ℝ)) := by
  unfold chart
  rw [lattice_plane]
  simp [planeRay]

lemma chart_plane_other (y : X) (i : Fin 6) (hi : i≠0) (p : Point) :
    (mirrorPlane (chart y i p)).1=0 ∨ (mirrorPlane (chart y i p)).2=0 := by
  unfold chart
  rw [lattice_plane]
  fin_cases i <;> simp_all [planeRay]

variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)

include hG hR
lemma chart_small {C : ℝ}
    (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
    (i : Fin 6) (p : Point) (hp : 0≤p.1 ∧ 0≤p.2) {w D : ℝ} (hw : D<w)
    (hx : |(mirrorPlane (chart y i p)).1-w|≤D)
    (hy : |(mirrorPlane (chart y i p)).2-w|≤D) :
    dist y (chart y i p•y) ≤ (rayLength y 0+rayLength y 1)*(w+D+1)+C := by
  have hi : i=0 := by
    by_contra hi
    rcases chart_plane_other y i hi p with h|h
    · rw [h] at hx
      linarith [(abs_le.mp hx).1]
    · rw [h] at hy
      linarith [(abs_le.mp hy).1]
  subst i
  rw [chart_plane_first] at hx hy
  have hL : 0<rayLength y 0 := ray_length_pos hG y hR 0
  have hM : 0<rayLength y 1 := ray_length_pos hG y hR 1
  have h1 := Int.lt_floor_add_one (p.1/rayLength y 0)
  have h2 := Int.lt_floor_add_one (p.2/rayLength y 1)
  have ha : p.1 < rayLength y 0*((⌊p.1/rayLength y 0⌋:ℝ)+1) := by
    have := (div_lt_iff₀ hL).mp h1
    nlinarith
  have hb : p.2 < rayLength y 1*((⌊p.2/rayLength y 1⌋:ℝ)+1) := by
    have := (div_lt_iff₀ hM).mp h2
    nlinarith
  have ha' : p.1≤rayLength y 0*(w+D+1) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hx).2 hL.le
    dsimp only at hh
    nlinarith
  have hb' : p.2≤rayLength y 1*(w+D+1) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 hM.le
    dsimp only at hh
    nlinarith
  have hh := (abs_le.mp (hchart 0 (0,0) p)).2
  simp only [chart_zero,one_smul,sub_zero] at hh
  have hv := vec_bound (cosine y 0) (cosine_abs hG y hR 0) p
  rw [abs_of_nonneg hp.1,abs_of_nonneg hp.2] at hv
  nlinarith

lemma circle_nonnegative {R t : ℝ} (hR0 : 0≤R) (i : Fin 6) (ht : t∈Set.Icc 0 1) :
    0≤R*(unit (cosine y i) t).1 ∧ 0≤R*(unit (cosine y i) t).2 := by
  have hu := unit_nonneg (cosine_lower hG y hR i).le (cosine_le_one hG y hR i) ht
  exact ⟨mul_nonneg hR0 hu.1,mul_nonneg hR0 hu.2⟩

lemma circle_first_sum {R t : ℝ} (hR0 : 0≤R) (ht : t∈Set.Icc 0 1) :
    R ≤ (rayLength y 0+rayLength y 1)*
      ((mirrorPlane (circle y R 0 t)).1+(mirrorPlane (circle y R 0 t)).2+2) := by
  let p : Point := (R*(unit (cosine y 0) t).1,R*(unit (cosine y 0) t).2)
  have hp : 0≤p.1 ∧ 0≤p.2 := circle_nonnegative hG y hR hR0 0 ht
  have hL : 0<rayLength y 0 := ray_length_pos hG y hR 0
  have hM : 0<rayLength y 1 := ray_length_pos hG y hR 1
  let a : ℝ := ⌊p.1/rayLength y 0⌋
  let b : ℝ := ⌊p.2/rayLength y 1⌋
  have ha : 0≤a := by
    change (0:ℝ)≤(⌊p.1/rayLength y 0⌋:ℝ)
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hp.1 hL.le)
  have hb : 0≤b := by
    change (0:ℝ)≤(⌊p.2/rayLength y 1⌋:ℝ)
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hp.2 hM.le)
  have h1 : p.1< (a+1)*rayLength y 0 := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one _)
  have h2 : p.2< (b+1)*rayLength y 1 := (div_lt_iff₀ hM).mp (Int.lt_floor_add_one _)
  have hsum : R≤p.1+p.2 := by
    have hh := mul_le_mul_of_nonneg_left (unit_sum (cosine_lower hG y hR 0).le (cosine_le_one hG y hR 0) ht).1 hR0
    dsimp only [p]
    nlinarith
  change R ≤ (rayLength y 0+rayLength y 1)*
    ((mirrorPlane (chart y 0 p)).1+(mirrorPlane (chart y 0 p)).2+2)
  rw [chart_plane_first]
  change R≤(rayLength y 0+rayLength y 1)*(a+b+2)
  nlinarith [mul_nonneg hL.le hb,mul_nonneg hM.le ha]

end SixSector
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

open scoped Classical
namespace ArtinCAT0.GridDisk
variable {H N : ℕ} [NeZero N]
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

omit [NeZero N] in
lemma rounded_edge_bound (y : X) (q : Vertex H N → X) (v : Vertex H N → G)
    {E B : ℝ} (hq : ∀ p, dist (q p) (v p•y)≤E)
    {p r : Vertex H N} (hpr : dist (q p) (q r)≤B) :
    dist (v p•y) (v r•y)≤B+2*E := by
  have hh := dist_triangle4 (v p•y) (q p) (q r) (v r•y)
  have hp := hq p
  rw [dist_comm] at hp
  linarith [hq r]

lemma cone_fill (hX : CAT0 X) (y : X) (base : G) (boundary : Fin N → G)
    {E A B R L : ℝ} (hE : 0≤E) (hA : 0≤A) (hB : 0≤B) (hL : 0≤L)
    (hdense : ∀ x, ∃ g : G, dist x (g•y)≤E)
    (hstep : ∀ i, dist (boundary i•y) (boundary (i+1)•y)≤A)
    (hspan : ∀ i, dist (base•y) (boundary i•y)≤(H+1:ℕ)*B)
    (hspan' : ∀ i, dist (base•y) (boundary i•y)≤L)
    (hbase : R≤dist y (base•y)) (hboundary : ∀ i, R≤dist y (boundary i•y)) :
    ∃ v : Vertex H N → G,
      (∀ i, v (Sum.inl (Fin.last (H+1),i)) = boundary i) ∧
      (∀ f k, dist (v (tail H N (f,k))•y) (v (tail H N (f,k+1))•y)≤A+B+4*E) ∧
      (∀ p, R-L/2-E≤dist y (v p•y)) := by
  choose round hround using hdense
  choose γ hγ using fun i => hX.1 (base•y) (boundary i•y)
  let v : Vertex H N → G := coneLabel base boundary γ round
  let q : Vertex H N → X := conePoint y base γ
  have hq : ∀ p, dist (q p) (v p•y)≤E := cone_approx y base boundary γ round hγ hE hround
  refine ⟨v,coneLabel_outer base boundary γ round,?_,?_⟩
  · have hh : ∀ f k, dist (v (tail H N (f,k))•y) (v (tail H N (f,k+1))•y)≤
        (A+2*E)+(B+2*E) := by
      apply edges_bound (fun p => v p•y) (by linarith) (by linarith)
      · intro r i
        exact rounded_edge_bound y q v hq (conePoint_horizontal y base boundary γ hγ hX hstep r i)
      · intro r i
        exact rounded_edge_bound y q v hq (conePoint_radial y base boundary γ hγ hspan r i)
      · intro i
        apply rounded_edge_bound y q v hq
        change dist (conePoint y base γ (Sum.inl (0,i) : Vertex H N)) (conePoint y base γ (Sum.inr ()))≤B
        rw [conePoint_center y base boundary γ hγ,dist_self]
        exact hB
    intro f k
    exact (hh f k).trans_eq (by ring)
  · exact coneLabel_radius y base boundary γ round hγ hE hround hbase hboundary hspan' hL

end ArtinCAT0.GridDisk

namespace ArtinCAT0.SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

abbrev AngularSize (n : ℕ) := 3*(2*(n+1))

def angularEquiv (n : ℕ) : Fin (AngularSize n) ≃ Fin (6*(n+1)) := finCongr (by dsimp [AngularSize]; omega)

@[simp] lemma angularEquiv_val (n : ℕ) (i : Fin (AngularSize n)) : (angularEquiv n i).val=i.val := rfl
@[simp] lemma angularEquiv_add (n : ℕ) (i j : Fin (AngularSize n)) :
    angularEquiv n (i+j) = angularEquiv n i+angularEquiv n j := by
  apply Fin.ext
  change (i.val+j.val) % (3*(2*(n+1))) = (i.val+j.val) % (6*(n+1))
  congr 1; omega

@[simp] lemma angularEquiv_one (n : ℕ) : angularEquiv n 1=1 := by
  apply Fin.ext
  change 1%(3*(2*(n+1)))=1%(6*(n+1))
  congr 1; omega

noncomputable def circleAt (y : X) (n : ℕ) (R : ℝ) (i : Fin (AngularSize n)) : TriangleGroup :=
  ringCircle y (n+1) R (angularEquiv n i)

noncomputable def innerLabel (y : X) (n : ℕ) : GridDisk.Vertex n (AngularSize n) → TriangleGroup
  | Sum.inl (r,i) => circleAt y n r.val i
  | Sum.inr _ => 1

@[simp] lemma circleAt_zero (y : X) (n : ℕ) (i : Fin (AngularSize n)) : circleAt y n 0 i=1 := by
  simp [circleAt,ringCircle,circle,axis]

variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C : ℝ} (hC : 0≤C)
  (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
include hG hR hC hchart

omit hC in
lemma circleAt_step (n : ℕ) {R : ℝ} (hR0 : 0≤R) (i : Fin (AngularSize n)) :
    dist (circleAt y n R i•y) (circleAt y n R (i+1)•y)≤20*R/(n+1:ℕ)+C := by
  simp only [circleAt,angularEquiv_add,angularEquiv_one]
  exact ringCircle_step hG y hR hchart (n+1) hR0 _

lemma innerLabel_edges (n : ℕ) :
    ∀ f k, dist (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k))•y)
      (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k+1))•y)≤21+2*C := by
  have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (by omega)
  have hh : ∀ f k, dist (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k))•y)
      (innerLabel y n (GridDisk.tail n (AngularSize n) (f,k+1))•y) ≤(20+C)+(1+C) := by
    apply GridDisk.edges_bound (fun p => innerLabel y n p•y) (by linarith) (by linarith)
    · intro r i
      have hh := circleAt_step hG y hR hchart n (Nat.cast_nonneg r.val) i
      have hr : (r.val:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show r.val≤n+1 by omega)
      change dist (circleAt y n r.val i•y) (circleAt y n r.val (i+1)•y)≤20+C
      apply hh.trans
      have hs : 20*(r.val:ℝ)/(n+1:ℕ)≤20 := (div_le_iff₀ hn).mpr (by nlinarith)
      linarith
    · intro r i
      have hh := ringCircle_radial hG y hR hchart (n+1) (r.succ.val) (r.castSucc.val) (angularEquiv n i)
      change dist (circleAt y n r.succ.val i•y) (circleAt y n r.castSucc.val i•y)≤1+C
      simpa only [circleAt,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,abs_one] using hh
    · intro i
      simp only [innerLabel,Fin.val_zero,Nat.cast_zero,circleAt_zero,one_smul,dist_self]
      linarith
  intro f k
  exact (hh f k).trans_eq (by ring)

omit hC hchart in
lemma innerLabel_chart (n : ℕ) (p : GridDisk.Vertex n (AngularSize n)) :
    ∃ i q, 0≤q.1 ∧ 0≤q.2 ∧ innerLabel y n p=chart y i q := by
  rcases p with ⟨r,j⟩|u
  · let e := finProdFinEquiv.symm (angularEquiv n j)
    let t : ℝ := e.2.val/(n+1:ℕ)
    have hp := unit_nonneg (cosine_lower hG y hR e.1).le (cosine_le_one hG y hR e.1)
      (angular_parameter e.2)
    exact ⟨e.1,((r.val:ℝ)*(unit (cosine y e.1) t).1,(r.val:ℝ)*(unit (cosine y e.1) t).2),
      mul_nonneg (Nat.cast_nonneg _) hp.1,mul_nonneg (Nat.cast_nonneg _) hp.2,rfl⟩
  · exact ⟨0,(0,0),le_rfl,le_rfl,(chart_zero y 0).symm⟩

end ArtinCAT0.SixSector
open scoped Classical
namespace ArtinCAT0
namespace RayIndex
noncomputable def shifted (w : ℝ) (p : Point) : Point := (p.1-w,p.2-w)

lemma edge_chain_equal {K : ℕ} (p : Fin (K+1) → Point)
    (hp : (∀ i, 0<(p i).1+(p i).2) ∨ (∀ i, (p i).1<0) ∨ (∀ i, (p i).2≤0)) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = edge (p 0) (p (Fin.last K)) := by
  rcases hp with h|h|h
  · rw [edge_chain_diagonal p h,edge_diagonal (h 0) (h (Fin.last K))]
  · rw [edge_chain_left p h,edge_left (h 0) (h (Fin.last K))]
  · rw [edge_chain_low p h,edge_low (h 0) (h (Fin.last K))]
end RayIndex

namespace TriangleMesh.Replacement
open RayIndex
variable {F V A U : Type*} (M : TriangleMesh F V) (P : TrianglePatch A U)
  {K : ℕ} [NeZero K] (S : P.Sides K)
omit [NeZero K] in
lemma edgeFlux_equal (p : Vertex M P S → Point) (q : V → Point) (f : F) (i : Fin 3)
    (hc : ∀ j, p (vertex M P S (f,S.point (j,0))) = q (M.tail (f,j)))
    (hp : (∀ j, 0<(p (vertex M P S (f,S.point (i,j)))).1+(p (vertex M P S (f,S.point (i,j)))).2) ∨
      (∀ j, (p (vertex M P S (f,S.point (i,j)))).1<0) ∨
      (∀ j, (p (vertex M P S (f,S.point (i,j)))).2≤0)) :
    edgeFlux M P S p f i = edge (q (M.tail (f,i))) (q (M.tail (f,i+1))) := by
  rw [edgeFlux,edge_chain_equal _ hp,hc]
  rw [S.ends,hc]
end TriangleMesh.Replacement

namespace SixSector
open SectorMetric RayIndex
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X]

lemma chart_plane_other_uniform (y : X) (i : Fin 6) (hi : i≠0) :
    (∀ p, (mirrorPlane (chart y i p)).1=0) ∨ (∀ p, (mirrorPlane (chart y i p)).2=0) := by
  simp_rw [chart,lattice_plane]
  fin_cases i <;> simp_all [planeRay]

variable [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
include hG hR

lemma ringCircle_next_product (N : ℕ) [NeZero N] (R : ℝ) (a : Fin 6) (j : Fin N) :
    ringCircle y N R (finProdFinEquiv (a,j)+1) = circle y R a ((j.val+1:ℕ)/N) := by
  rw [product_next]
  split_ifs with h
  · exact ringCircle_product y N R a ⟨j.val+1,h⟩
  · have hj : j.val+1=N := by omega
    rw [ringCircle_product,hj,div_self (by exact_mod_cast (NeZero.ne N)),circle_one hG y hR]
    simp only [Fin.val_zero,Nat.cast_zero,zero_div,circle_zero]

lemma circle_shift_diagonal {R w t : ℝ} (hR0 : 0≤R) (ht : t∈Set.Icc 0 1)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) :
    0<(shifted w (mirrorPlane (circle y R 0 t))).1+
      (shifted w (mirrorPlane (circle y R 0 t))).2 := by
  have hh := circle_first_sum hG y hR hR0 ht
  have hL : 0<rayLength y 0+rayLength y 1 := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
  dsimp only [shifted]
  have hs : 2*w < (mirrorPlane (circle y R 0 t)).1+(mirrorPlane (circle y R 0 t)).2 := by
    nlinarith
  linarith

lemma circle_chain_index (N : ℕ) [NeZero N] {R w : ℝ} (hR0 : 0≤R) (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) (a : Fin 6) :
    (∑ j : Fin N, edge (shifted w (mirrorPlane (circle y R a (j.val/N))))
      (shifted w (mirrorPlane (circle y R a ((j.val+1:ℕ)/N))))) = if a=0 then 1 else 0 := by
  let p : Fin (N+1) → RayIndex.Point := fun j => shifted w (mirrorPlane (circle y R a (j.val/N)))
  have ht (j : Fin (N+1)) : (j.val/(N:ℝ))∈Set.Icc 0 1 := by
    have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
    exact ⟨div_nonneg (Nat.cast_nonneg _) hN.le,(div_le_iff₀ hN).mpr (by rw [one_mul]; exact_mod_cast (show j.val≤N by omega))⟩
  change (∑ j : Fin N, edge (p j.castSucc) (p j.succ)) = _
  by_cases ha : a=0
  · subst a
    rw [ite_eq_left rfl,edge_chain_diagonal p (fun j => circle_shift_diagonal hG y hR hR0 (ht j) hlarge)]
    have hp0 : (p 0).2 = -w := by
      dsimp only [p,shifted]
      simp only [Fin.val_zero,Nat.cast_zero,zero_div,circle_zero]
      rw [← chart_axis1 y 0 R,chart_plane_first]
      simp
    have hplast : (p (Fin.last N)).1 = -w := by
      dsimp only [p,shifted]
      rw [Fin.val_last,div_self (by exact_mod_cast (NeZero.ne N)),circle_one hG y hR]
      rw [← chart_axis2 y 0 R,chart_plane_first]
      simp
    have hd := circle_shift_diagonal hG y hR hR0 (ht (Fin.last N)) hlarge
    change 0<(p (Fin.last N)).1+(p (Fin.last N)).2 at hd
    rw [hplast] at hd
    have hp : 0<(p (Fin.last N)).2 := by linarith
    simp [above,hp,hp0,hw.le]
  · rw [ite_eq_right ha]
    rcases chart_plane_other_uniform y a ha with h|h
    · apply edge_chain_left p
      intro j
      change (mirrorPlane (chart y a _)).1-w<0
      rw [h]
      linarith
    · apply edge_chain_low p
      intro j
      change (mirrorPlane (chart y a _)).2-w≤0
      rw [h]
      linarith

lemma ringCircle_index (N : ℕ) [NeZero N] {R w : ℝ} (hR0 : 0≤R) (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) :
    (∑ j : Fin (6*N), edge (shifted w (mirrorPlane (ringCircle y N R j)))
      (shifted w (mirrorPlane (ringCircle y N R (j+1))))) = 1 := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  simp_rw [ringCircle_product,ringCircle_next_product hG y hR]
  simp_rw [circle_chain_index hG y hR N hR0 hw hlarge]
  simp

end SixSector
end ArtinCAT0

namespace ArtinCAT0.GridDisk
open RayIndex
variable (H N : ℕ) [NeZero N]
lemma sum_index_boundary (p : Vertex H N → Point) :
    (∑ f, face (fun i => p (tail H N (f,i)))) = ∑ j : Fin N,
      edge (p (Sum.inl (Fin.last (H+1),j))) (p (Sum.inl (Fin.last (H+1),j+1))) := by
  classical
  let w (d : Face H N × Fin 3) := edge (p (tail H N d)) (p (tail H N (d.1,d.2+1)))
  have ha (d) (hd : ¬(patch H N).Boundary d) : w ((patch H N).mate d) = -w d := by
    dsimp only [w]
    change edge (p ((patch H N).tail ((patch H N).mate d)))
      (p ((patch H N).tail (((patch H N).mate d).1,((patch H N).mate d).2+1))) = _
    rw [(patch H N).tail_mate d hd,(patch H N).tail_rotate_mate d hd]
    exact edge_reverse _ _
  change (∑ f, ∑ i, w (f,i)) = _
  rw [(patch H N).sum_faces_boundary w ha,← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => (A H N (Fin.last H) j,0))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(boundary_iff H N _).mpr ⟨j,rfl⟩⟩
  · intro j _ k _ hjk
    simpa only [Prod.mk.injEq,A,Sum.inl.injEq,true_and,and_true] using hjk
  · intro d hd
    obtain ⟨j,rfl⟩ := (boundary_iff H N _).mp (Finset.mem_filter.mp hd).2
    exact ⟨j,Finset.mem_univ _,rfl⟩
  · intro j _
    rfl
end ArtinCAT0.GridDisk

namespace ArtinCAT0.SixSector
open SectorMetric RayIndex
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
include hG hR
lemma circleAt_index (n : ℕ) {R w : ℝ} (hR0 : 0≤R) (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<R) :
    (∑ j : Fin (AngularSize n), edge (shifted w (mirrorPlane (circleAt y n R j)))
      (shifted w (mirrorPlane (circleAt y n R (j+1))))) = 1 := by
  have hh := Equiv.sum_comp (angularEquiv n) (fun j => edge (shifted w (mirrorPlane (ringCircle y (n+1) R j)))
    (shifted w (mirrorPlane (ringCircle y (n+1) R (j+1)))))
  simp only [circleAt,angularEquiv_add,angularEquiv_one]
  exact hh.trans (ringCircle_index hG y hR (n+1) hR0 hw hlarge)

lemma innerLabel_index (n : ℕ) {w : ℝ} (hw : 0<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2)<(n+1:ℕ)) :
    (∑ f, face (fun i => shifted w (mirrorPlane (innerLabel y n (GridDisk.tail n (AngularSize n) (f,i)))))) = 1 := by
  rw [GridDisk.sum_index_boundary n (AngularSize n) (fun p => shifted w (mirrorPlane (innerLabel y n p)))]
  simpa only [innerLabel,Fin.val_last] using circleAt_index hG y hR n (Nat.cast_nonneg (n+1)) hw hlarge
end ArtinCAT0.SixSector
open scoped Classical
namespace ArtinCAT0.SixSector
open SectorMetric
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
  {C E d : ℝ} (hC : 0≤C) (hE : 0≤E) (hd : 0≤d) (hd2 : d<2)
  (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
  (hdense : ∀ x, ∃ g : TriangleGroup, dist x (g•y)≤E)
  (hdetour : ∀ R : ℝ, 0≤R → ∀ i t, t∈Set.Icc 0 1 →
    dist (axis y 0 R•y) (circle y R i t•y)≤d*R+3*C)
include hG hR hC hE hd hd2 hchart hdense hdetour

lemma cap_exists (n : ℕ) :
    ∃ v : GridDisk.Vertex n (AngularSize n) → TriangleGroup,
      (∀ i, v (Sum.inl (Fin.last (n+1),i)) = circleAt y n (n+1:ℕ) (-i)) ∧
      (∀ f k, dist (v (GridDisk.tail n (AngularSize n) (f,k))•y)
        (v (GridDisk.tail n (AngularSize n) (f,k+1))•y)≤22+4*C+4*E) ∧
      (∀ p, (1-d/2)*(n+1:ℕ)-5*C/2-E≤dist y (v p•y)) := by
  let R : ℝ := (n+1:ℕ)
  have hR1 : 1≤R := by dsimp [R]; exact_mod_cast (show 1≤n+1 by omega)
  have hR0 : 0≤R := by linarith
  let b : Fin (AngularSize n) → TriangleGroup := fun i => circleAt y n R (-i)
  have hstep (i) : dist (b i•y) (b (i+1)•y)≤20+C := by
    have hh := circleAt_step hG y hR hchart n hR0 (-i-1)
    have he : -i-1+1 = -i := sub_add_cancel _ _
    rw [he] at hh
    change dist (circleAt y n R (-i)•y) (circleAt y n R (-(i+1))•y)≤20+C
    rw [dist_comm]
    have hz : -(i+1) = -i-1 := by abel
    rw [hz]
    apply hh.trans
    have hRp : R ≠ 0 := by linarith
    change 20*R/R+C≤20+C
    rw [mul_div_cancel_right₀ 20 hRp]
  have hspan' (i) : dist (axis y 0 R•y) (b i•y)≤d*R+3*C :=
    hdetour R hR0 _ _ (angular_parameter _)
  have hspan (i) : dist (axis y 0 R•y) (b i•y)≤(n+1:ℕ)*(2+3*C) := by
    have hh := hspan' i
    have hmul := mul_nonneg (sub_nonneg.mpr hR1) hC
    dsimp only [R] at *
    nlinarith
  have hbase : R-C≤dist y (axis y 0 R•y) := by
    have hh := (abs_le.mp (axis_radius hG y hR hchart hR0 0)).1
    linarith
  have hb (i) : R-C≤dist y (b i•y) := by
    have hh := (abs_le.mp (ringCircle_radius hG y hR hchart (n+1) hR0 (angularEquiv n (-i)))).1
    change -(C) ≤ dist y (b i•y)-R at hh
    linarith
  obtain ⟨v,hv,he,hr⟩ := GridDisk.cone_fill (H:=n) hG.1 y (axis y 0 R) b hE
    (by linarith : 0≤20+C) (by linarith : 0≤2+3*C) (by positivity : 0≤d*R+3*C)
    hdense hstep hspan hspan' hbase hb
  refine ⟨v,hv,?_,?_⟩
  · intro f k
    exact (he f k).trans_eq (by ring)
  · intro p
    have hh := hr p
    change R-C-(d*R+3*C)/2-E≤dist y (v p•y) at hh
    dsimp only [R] at hh
    linarith

end ArtinCAT0.SixSector
open scoped Classical
namespace ArtinCAT0
noncomputable def mirrorAt (w : ℝ) (g : TriangleGroup) : RayIndex.Point :=
  ((mirrorPlane g).1-w,(mirrorPlane g).2-w)

namespace SixSector
open SectorMetric TriangleMesh
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
variable {F V A U : Type*} [Fintype F] [Fintype A]
  (M : TriangleMesh F V) (P : TrianglePatch A U) {K : ℕ} [NeZero K] (S : P.Sides K)
  (z : V → TriangleGroup) (L : (Replacement.mesh M P S).SimplicialLabeling)
  (Q : F → Prop) [DecidablePred Q]

include hG hR
lemma refined_index_zero (hM : M.Exact) (hP : P.Exact)
    {C C₀ D w R : ℝ} (hw : D+1<w)
    (hchart : ∀ i p q, |dist (chart y i p•y) (chart y i q•y)-
      ‖vec (cosine y i) (q.1-p.1,q.2-p.2)‖|≤C)
    (hmetric : ∀ f p, dist (L.vertex (Replacement.vertex M P S (f,p))•y) (z (M.tail (f,0))•y)≤C₀)
    (hmirror : ∀ f p d, |mirrorVector (L.vertex (Replacement.vertex M P S (f,p))) d-
      mirrorVector (z (M.tail (f,0))) d|≤D)
    (hinner : ∀ f, Q f → ∃ i p, 0≤p.1 ∧ 0≤p.2 ∧ z (M.tail (f,0))=chart y i p)
    (houter : ∀ f, ¬Q f → R≤dist y (z (M.tail (f,0))•y))
    (hgap : (rayLength y 0+rayLength y 1)*(w+D+2)+C+2*C₀<R) :
    (∑ f : F × A, if Q f.1 then RayIndex.occurrence (Replacement.mesh M P S) L (mirrorAt w) f else 0) = 0 := by
  apply RayIndex.localized_zero _ L (mirrorAt w) (Replacement.exact M P S hM hP) (fun f => Q f.1)
  intro f g hf hn he hg
  by_contra hng
  let b := z (M.tail (f.1,0))
  have hclose (i : Fin 3) :
      |(mirrorAt w (L.vertex ((Replacement.mesh M P S).tail (f,i)))).1-(mirrorAt w b).1|<D+1 ∧
      |(mirrorAt w (L.vertex ((Replacement.mesh M P S).tail (f,i)))).2-(mirrorAt w b).2|<D+1 := by
    have hh := mirrorPlane_close (hmirror f.1 (P.tail (f.2,i)))
    dsimp only [mirrorAt]
    simp only [sub_sub_sub_cancel_right]
    exact ⟨lt_of_le_of_lt hh.1 (by linarith),lt_of_le_of_lt hh.2 (by linarith)⟩
  have hloc := RayIndex.face_local hn (mirrorAt w b) hclose
  obtain ⟨i,p,hp,hp',hb⟩ := hinner f.1 hf
  have hb' : b=chart y i p := hb
  have hsmall : dist y (b•y)≤(rayLength y 0+rayLength y 1)*(w+D+2)+C := by
    have hx : |(mirrorPlane (chart y i p)).1-w|≤D+1 := by
      simpa only [mirrorAt,hb'] using hloc.1.le
    have hy : |(mirrorPlane (chart y i p)).2-w|≤D+1 := by
      simpa only [mirrorAt,hb'] using hloc.2.le
    rw [hb']
    have hh := chart_small hG y hR hchart i p ⟨hp,hp'⟩ hw hx hy
    convert hh using 1
    ring
  obtain ⟨j,hj⟩ := Finite.surjective_of_injective hg (L.corner f 0)
  have hv : L.vertex ((Replacement.mesh M P S).tail (f,0)) =
      L.vertex ((Replacement.mesh M P S).tail (g,j)) := by
    rw [L.vertex_tail,L.vertex_tail,he,hj]
  have hmf := hmetric f.1 (P.tail (f.2,0))
  have hmg := hmetric g.1 (P.tail (g.2,j))
  have htri := dist_triangle y (L.vertex ((Replacement.mesh M P S).tail (f,0))•y) (z (M.tail (g.1,0))•y)
  have htri' := dist_triangle y (b•y) (L.vertex ((Replacement.mesh M P S).tail (f,0))•y)
  change dist (L.vertex ((Replacement.mesh M P S).tail (f,0))•y) (b•y)≤C₀ at hmf
  change dist (L.vertex ((Replacement.mesh M P S).tail (g,j))•y) (z (M.tail (g.1,0))•y)≤C₀ at hmg
  rw [← hv] at hmg
  rw [dist_comm (b•y)] at htri'
  have ho := houter g.1 hng
  linarith

end SixSector
end ArtinCAT0
open scoped Classical
namespace ArtinCAT0.SixSector
open SectorMetric RayIndex TriangleMesh
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]
variable (hG : GeometricAction TriangleGroup X) (y : X) (hR : StrictRatios y)
include hG hR

lemma circle_refined_side {R w D : ℝ} (hR0 : 0≤R) (hw : D<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2*D+2)<R)
    (a : Fin 6) {t : ℝ} (ht : t∈Set.Icc 0 1)
    {I : Type*} (v : I → TriangleGroup)
    (hv : ∀ j d, |mirrorVector (v j) d-mirrorVector (circle y R a t) d|≤D) :
    (∀ j, 0<(mirrorAt w (v j)).1+(mirrorAt w (v j)).2) ∨
      (∀ j, (mirrorAt w (v j)).1<0) ∨ (∀ j, (mirrorAt w (v j)).2≤0) := by
  have hc j := mirrorPlane_close (hv j)
  by_cases ha : a=0
  · subst a
    left
    intro j
    have hh := circle_first_sum hG y hR hR0 ht
    have hL := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
    change 0<rayLength y 0+rayLength y 1 at hL
    have hs : 2*w+2*D < (mirrorPlane (circle y R 0 t)).1+(mirrorPlane (circle y R 0 t)).2 := by
      nlinarith
    have hx := (abs_le.mp (hc j).1).1
    have hy := (abs_le.mp (hc j).2).1
    dsimp only [mirrorAt]
    linarith
  · right
    rcases chart_plane_other y a ha (R*(unit (cosine y a) t).1,R*(unit (cosine y a) t).2) with hx|hy
    · left
      intro j
      have hh := (abs_le.mp (hc j).1).2
      change (mirrorPlane (circle y R a t)).1=0 at hx
      rw [hx] at hh
      dsimp only [mirrorAt]
      linarith
    · right
      intro j
      have hh := (abs_le.mp (hc j).2).2
      change (mirrorPlane (circle y R a t)).2=0 at hy
      rw [hy] at hh
      dsimp only [mirrorAt]
      linarith

lemma refined_inner_index (n : ℕ)
    (v : GridDisk.Vertex n (AngularSize n) → TriangleGroup)
    (hv : ∀ i, innerLabel y n (Sum.inl (Fin.last (n+1),i)) = v (Sum.inl (Fin.last (n+1),-i)))
    {A U : Type*} [Fintype A] (P : TrianglePatch A U) {K : ℕ} [NeZero K] (S : P.Sides K)
    (L : (Replacement.mesh (GridSphere.mesh n (2*(n+1))) P S).SimplicialLabeling)
    {D w : ℝ} (hD : 0≤D) (hw : D<w)
    (hlarge : (rayLength y 0+rayLength y 1)*(2*w+2*D+2)<(n+1:ℕ))
    (hmirror : ∀ f p d, |mirrorVector (L.vertex (Replacement.vertex (GridSphere.mesh n (2*(n+1))) P S (f,p))) d-
      mirrorVector (GridSphere.label n (2*(n+1)) (innerLabel y n) v hv ((GridSphere.mesh n (2*(n+1))).tail (f,0))) d|≤D)
    (hcorner : ∀ f i, L.vertex (Replacement.vertex (GridSphere.mesh n (2*(n+1))) P S (f,S.point (i,0))) =
      GridSphere.label n (2*(n+1)) (innerLabel y n) v hv ((GridSphere.mesh n (2*(n+1))).tail (f,i))) :
    (∑ f : GridSphere.Face n (2*(n+1)) × A, if f.1.1=false then
      occurrence (Replacement.mesh (GridSphere.mesh n (2*(n+1))) P S) L (mirrorAt w) f else 0) = 1 := by
  let M := GridSphere.mesh n (2*(n+1))
  let z := GridSphere.label n (2*(n+1)) (innerLabel y n) v hv
  let p := fun u => mirrorAt w (L.vertex u)
  let q := fun u => mirrorAt w (z u)
  have hb (f) (i) (hf : f.1=false) (hgf : (M.mate (f,i)).1.1≠false) :
      Replacement.edgeFlux M P S p f i = edge (q (M.tail (f,i))) (q (M.tail (f,i+1))) := by
    rcases f with ⟨b,f⟩
    change b=false at hf
    subst b
    have hbd := (GridSphere.frontier n (2*(n+1)) (false,f) i).mp ⟨rfl,hgf⟩
    obtain ⟨j,hj⟩ := (GridDisk.boundary_iff n (AngularSize n) (f,i)).mp hbd.2
    cases hj
    apply Replacement.edgeFlux_equal M P S p q
    · intro k
      exact congrArg (mirrorAt w) (hcorner _ k)
    · let e := finProdFinEquiv.symm (angularEquiv n j)
      apply circle_refined_side hG y hR (Nat.cast_nonneg (n+1)) hw hlarge e.1 (angular_parameter e.2)
        (fun k => L.vertex (Replacement.vertex M P S ((false,GridDisk.A n (AngularSize n) (Fin.last n) j),S.point (0,k))))
      intro k d
      exact hmirror _ _ d
  have he := Replacement.region_index M P S (fun f => f.1=false) p q hb
  change (∑ f : GridSphere.Face n (2*(n+1)) × A, if f.1.1=false then
    face (fun i => p ((Replacement.mesh M P S).tail (f,i))) else 0) = 1
  rw [he,GridSphere.inner_sum]
  have hwin := innerLabel_index hG y hR n (lt_of_le_of_lt hD hw)
    (show (rayLength y 0+rayLength y 1)*(2*w+2)<(n+1:ℕ) from by
      have hL := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
      nlinarith)
  exact hwin

end ArtinCAT0.SixSector

namespace ArtinCAT0.SixSector
open SectorMetric TriangleMesh
variable {X : Type*} [MetricSpace X] [MulAction TriangleGroup X] [ProperSpace X] [Nonempty X]

theorem no_strict_ratios (hG : GeometricAction TriangleGroup X) (y : X) : ¬StrictRatios y := by
  classical
  intro hR
  obtain ⟨C,hC,hchart⟩ := chart_uniform hG y hR
  obtain ⟨E,hE,hdense⟩ := orbit_uniformly_dense hG y
  obtain ⟨c,hc,hc1,hcos⟩ := common_cosine hG y hR
  obtain ⟨r,hr,_,_,hd2⟩ := detour_gap hc hc1
  let d : ℝ := 2*Real.sqrt (1+r^2-2*c*r)+r
  have hd : 0≤d := by dsimp [d]; positivity
  have hdetour : ∀ R : ℝ, 0≤R → ∀ i t, t∈Set.Icc 0 1 →
      dist (axis y 0 R•y) (circle y R i t•y)≤d*R+3*C := by
    intro R hR0 i t ht
    exact circle_detour hG y hR hC hchart hcos hr.le hR0 i ht
  let B := 22+4*C+4*E
  have hB : 0≤B := by dsimp [B]; positivity
  obtain ⟨K,H,hK,hlib⟩ := WordDiagram.controlled_refinement hG y B hB
  let : NeZero K := ⟨by omega⟩
  obtain ⟨C₀,D,hC₀,hD,hlib⟩ := hlib
  let w := D+2
  let a := 1-d/2
  let T := rayLength y 0+rayLength y 1
  have ha : 0<a := by dsimp [a,d]; linarith
  have hT : 0<T := add_pos (ray_length_pos hG y hR 0) (ray_length_pos hG y hR 1)
  obtain ⟨n,hn⟩ := exists_nat_gt (max (T*(2*w+2*D+2)) ((T*(w+D+2)+C+2*C₀+5*C/2+E)/a))
  have hn1 : T*(2*w+2*D+2)<(n+1:ℕ) := by
    have hh := lt_of_le_of_lt (le_max_left (T*(2*w+2*D+2)) _) hn
    push_cast
    linarith
  have hn2 : T*(w+D+2)+C+2*C₀ < (1-d/2)*(n+1:ℕ)-5*C/2-E := by
    have hh := lt_of_le_of_lt (le_max_right (T*(2*w+2*D+2)) _) hn
    have hh' := (div_lt_iff₀ ha).mp hh
    dsimp only [a] at ha hh'
    push_cast
    nlinarith
  obtain ⟨v,hv,hve,hvr⟩ := cap_exists hG y hR hC hE hd hd2 hchart hdense hdetour n
  have hagree (i) : innerLabel y n (Sum.inl (Fin.last (n+1),i)) = v (Sum.inl (Fin.last (n+1),-i)) := by
    rw [hv]
    simp only [neg_neg,innerLabel,Fin.val_last]
  let M := GridSphere.mesh n (2*(n+1))
  let z := GridSphere.label n (2*(n+1)) (innerLabel y n) v hagree
  have hedge : ∀ f i, dist (z (M.tail (f,i))•y) (z (M.tail (f,i+1))•y)≤B := by
    apply GridSphere.edges n (2*(n+1)) (innerLabel y n) v hagree (fun g => g•y)
    · intro f i
      exact (innerLabel_edges hG y hR hC hchart n f i).trans (by dsimp [B]; linarith)
    · exact hve
  obtain ⟨L,hmetric,hmirror,hcorner⟩ := hlib _ _ M z hedge
  let P := GridDisk.patch H (3*K)
  let S := GridDisk.sides H K
  have hone := refined_inner_index hG y hR n v hagree P S L hD
    (show D<w by dsimp [w]; linarith) hn1 hmirror hcorner
  have hinner (f : GridSphere.Face n (2*(n+1))) (hf : f.1=false) :
      ∃ i p, 0≤p.1 ∧ 0≤p.2 ∧ z (M.tail (f,0))=chart y i p := by
    rcases f with ⟨b,f⟩
    change b=false at hf
    subst b
    exact innerLabel_chart hG y hR n (GridDisk.tail n (AngularSize n) (f,0))
  have houter (f : GridSphere.Face n (2*(n+1))) (hf : ¬f.1=false) :
      (1-d/2)*(n+1:ℕ)-5*C/2-E≤dist y (z (M.tail (f,0))•y) := by
    rcases f with ⟨b,f⟩
    cases b
    · exact False.elim (hf rfl)
    · exact hvr (GridDisk.tail n (AngularSize n) (f,0))
  have hzero := refined_index_zero hG y hR M P S z L (fun f => f.1=false)
    (GridSphere.exact n (2*(n+1))) (GridDisk.exact H (3*K))
    (show D+1<w by dsimp [w]; linarith) hchart hmetric hmirror hinner houter hn2
  have hs : (1:ℤ)=0 := hone.symm.trans hzero
  norm_num at hs

end ArtinCAT0.SixSector

end OAI
end
end

section
section
namespace OAI

open scoped Classical
namespace ArtinCAT0.AmalgamTools
open Monoid Monoid.CoprodI Monoid.PushoutI Monoid.PushoutI.NormalWord
variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
variable {φ : ∀ i, H →* G i}

lemma reduced_append {i j k l : ι} (a : NeWord G i j) (h : j≠k) (b : NeWord G k l) :
    Reduced φ (a.append h b).toWord ↔ Reduced φ a.toWord ∧ Reduced φ b.toWord := by
  simp only [Reduced,NeWord.toWord,NeWord.toList,List.mem_append]
  aesop

lemma reduced_singleton {i : ι} (g : G i) (hg : g≠1) :
    Reduced φ (NeWord.singleton g hg).toWord ↔ g∉(φ i).range := by
  simp [Reduced,NeWord.toWord]

lemma reduced_inv {i j : ι} (a : NeWord G i j) (ha : Reduced φ a.toWord) :
    Reduced φ a.inv.toWord := by
  induction a with
  | singleton g hg =>
    simpa only [NeWord.inv,reduced_singleton,inv_mem_iff] using (reduced_singleton g hg).mp ha
  | append a h b iha ihb =>
    rw [reduced_append] at ha
    exact (reduced_append _ _ _).mpr ⟨ihb ha.2,iha ha.1⟩

lemma reduced_not_factor (hφ : ∀ i, Function.Injective (φ i))
    {w : Word G} (hw : Reduced φ w) {k : ι}
    (hk : ∃ g∈w.toList, g.1≠k) : ofCoprodI (φ:=φ) w.prod ∉ (PushoutI.of k).range := by
  rintro ⟨b,hb⟩
  by_cases hr : b∈(φ k).range
  · obtain ⟨c,hc⟩ := hr
    have he := hw.eq_empty_of_mem_range hφ ⟨c,by rw [← hc,of_apply_eq_base] at hb; exact hb⟩
    subst w
    simp [Word.empty] at hk
  · obtain ⟨d⟩ := transversal_nonempty φ hφ
    obtain ⟨w',hw',htypes⟩ := hw.exists_normalWord_prod_eq d
    let b' : NormalWord d := NormalWord.cons b NormalWord.empty (by change (none : Option ι) ≠ some k; intro h; cases h) hr
    have hb' : b'.prod=PushoutI.of k b := by
      dsimp only [b']
      rw [NormalWord.prod_cons,NormalWord.prod_empty,mul_one]
    have he : w'=b' := NormalWord.prod_injective (hw'.trans (hb.symm.trans hb'.symm))
    rw [he] at htypes
    obtain ⟨g,hg,hgk⟩ := hk
    have hh : g.1 ∈ w.toList.map Sigma.fst := List.mem_map.mpr ⟨g,hg,rfl⟩
    rw [← htypes] at hh
    have hh' : g.1=k := by
      simpa [b',NormalWord.cons,Word.cons,NormalWord.empty,Word.empty] using hh
    exact hgk hh'

/-- A reduced word is either a single-factor element, or conjugating an element
whose factor-conjugacy class avoids the base produces a reduced word still
containing a letter from another factor. -/
lemma conjugate_certificate {k i j : ι} (w : NeWord G i j) (hw : Reduced φ w.toWord) :
    (∃ b : G k, ofCoprodI (φ:=φ) w.prod=PushoutI.of k b ∧ i=k ∧ j=k) ∨
    (∀ q : G k, (∀ b : G k, b*q*b⁻¹∉(φ k).range) →
      ∃ v : NeWord G i i, Reduced φ v.toWord ∧
        ofCoprodI (φ:=φ) v.prod = ofCoprodI (φ:=φ) w.prod * PushoutI.of k q *
          (ofCoprodI (φ:=φ) w.prod)⁻¹ ∧ ∃ g∈v.toList, g.1≠k) := by
  induction w with
  | @singleton i g hg =>
    by_cases hi : i=k
    · subst i
      exact Or.inl ⟨g,by simp,rfl,rfl⟩
    · right
      intro q hq
      have hqr : q∉(φ k).range := by simpa using hq 1
      have hq1 : q≠1 := fun he => hqr (he ▸ (φ k).range.one_mem)
      let a : NeWord G i i := .singleton g hg
      let b : NeWord G k k := .singleton q hq1
      let v := (a.append hi b).append (Ne.symm hi) a.inv
      refine ⟨v,(reduced_append _ _ _).mpr ⟨(reduced_append _ _ _).mpr
        ⟨hw,(reduced_singleton q hq1).mpr hqr⟩,reduced_inv a hw⟩,?_,?_⟩
      · simp [v,a,b]
      · exact ⟨⟨i,g⟩,by simp [v,a],hi⟩
  | @append i j l m a h b iha ihb =>
    obtain ⟨ha,hb⟩ := (reduced_append a h b).mp hw
    rcases ihb hb with ⟨c,hc,hl,hm⟩ | hcb
    · subst l; subst m
      rcases iha ha with ⟨e,he,hi,hj⟩ | hca
      · exact False.elim (h hj)
      · right
        intro q hq
        obtain ⟨v,hv,hvp,hvm⟩ := hca (c*q*c⁻¹) (by
          intro e
          convert hq (e*c) using 1; group)
        refine ⟨v,hv,?_,hvm⟩
        simp only [hvp,NeWord.append_prod,map_mul,map_inv,hc]
        group
    · right
      intro q hq
      obtain ⟨v,hv,hvp,hvm⟩ := hcb q hq
      let u := (a.append h v).append h.symm a.inv
      refine ⟨u,(reduced_append _ _ _).mpr ⟨(reduced_append _ _ _).mpr ⟨ha,hv⟩,
        reduced_inv a ha⟩,?_,?_⟩
      · simp only [u,NeWord.append_prod,NeWord.inv_prod,map_mul,map_inv,hvp]
        group
      · obtain ⟨g,hg,hgk⟩ := hvm
        exact ⟨g,by simp only [u,NeWord.toList,List.mem_append]; exact Or.inl (Or.inr hg),hgk⟩

lemma normal_reduced (d : Transversal φ) (w : NormalWord d) : Reduced φ w.toWord := by
  rintro ⟨i,g⟩ hg hr
  have hself := (Subgroup.IsComplement.equiv_snd_eq_self_iff_mem (d.compl i) (φ i).range.one_mem).mpr
    (w.normalized i g hg)
  have hone := (Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem (d.compl i) (d.one_mem i)).mpr hr
  exact w.ne_one ⟨i,g⟩ hg (hself.symm.trans hone)

/-- Centralizers cannot escape the factor when the factor-conjugacy class
of the element misses the amalgamating subgroup. -/
theorem centralizer_in_factor (hφ : ∀ i, Function.Injective (φ i)) (k : ι) (q : G k)
    (hq : ∀ b : G k, b*q*b⁻¹∉(φ k).range)
    (g : PushoutI φ) (hg : Commute g (PushoutI.of k q)) : g∈(PushoutI.of k).range := by
  classical
  obtain ⟨d⟩ := transversal_nonempty φ hφ
  let w : NormalWord d := NormalWord.equiv g
  have hwp : w.prod=g := (NormalWord.equiv (d:=d)).symm_apply_apply g
  have hp : PushoutI.base φ w.head * ofCoprodI (φ:=φ) w.toWord.prod=g := hwp
  have hh : PushoutI.base φ w.head ∈ (PushoutI.of k).range :=
    ⟨φ k w.head,of_apply_eq_base φ k w.head⟩
  by_cases he : w.toWord=Word.empty
  · have hgg : g=PushoutI.base φ w.head := by simpa [he] using hp.symm
    exact hgg ▸ hh
  · obtain ⟨i,j,v,hv⟩ := NeWord.of_word w.toWord he
    have hvr : Reduced φ v.toWord := hv.symm ▸ normal_reduced d w
    rcases conjugate_certificate (k:=k) v hvr with ⟨b,hb,_,_⟩ | hc
    · rw [← hv] at hp
      change PushoutI.base φ w.head * ofCoprodI (φ:=φ) v.prod=g at hp
      have hbmem : ofCoprodI (φ:=φ) v.prod∈(PushoutI.of (φ:=φ) k).range := ⟨b,hb.symm⟩
      exact hp ▸ (PushoutI.of (φ:=φ) k).range.mul_mem hh hbmem
    · obtain ⟨u,hur,hup,hum⟩ := hc q hq
      have hnot := reduced_not_factor hφ hur hum
      apply False.elim
      apply hnot
      change ofCoprodI (φ:=φ) u.prod∈(PushoutI.of (φ:=φ) k).range
      rw [hup]
      have hp' : ofCoprodI (φ:=φ) v.prod=(PushoutI.base φ w.head)⁻¹*g := by
        rw [← hp,← hv]
        simp [NeWord.prod]
      rw [hp']
      have hg' : g * PushoutI.of k q * g⁻¹=PushoutI.of k q := hg.mul_inv_cancel
      have hh' : (PushoutI.base φ w.head)⁻¹*g*PushoutI.of k q*
          ((PushoutI.base φ w.head)⁻¹*g)⁻¹ =
          (PushoutI.base φ w.head)⁻¹*PushoutI.of k q*PushoutI.base φ w.head := by
        calc
          _ = (PushoutI.base φ w.head)⁻¹*(g*PushoutI.of k q*g⁻¹)*PushoutI.base φ w.head := by group
          _ = _ := by rw [hg']
      rw [hh']
      exact (PushoutI.of (φ:=φ) k).range.mul_mem ((PushoutI.of (φ:=φ) k).range.mul_mem
        ((PushoutI.of (φ:=φ) k).range.inv_mem hh) ⟨q,rfl⟩) hh

end ArtinCAT0.AmalgamTools

namespace ArtinCAT0.BinaryAmalgam
open Monoid
variable {A B H K : Type u} [Group A] [Group B] [Group H] [Group K]
def Family (A B : Type u) : Bool → Type u
  | false => A
  | true => B
instance familyGroup : ∀ i, Group (Family A B i)
  | false => inferInstanceAs (Group A)
  | true => inferInstanceAs (Group B)
def diagram (f : H →* A) (g : H →* B) : ∀ i, H →* Family A B i
  | false => f
  | true => g
abbrev GroupOf (f : H →* A) (g : H →* B) := PushoutI (diagram f g)
def left (f : H →* A) (g : H →* B) : A →* GroupOf f g := PushoutI.of (φ:=diagram f g) false
def right (f : H →* A) (g : H →* B) : B →* GroupOf f g := PushoutI.of (φ:=diagram f g) true
lemma agree (f : H →* A) (g : H →* B) : (left f g).comp f=(right f g).comp g := by
  exact (PushoutI.of_comp_eq_base (φ:=diagram f g) false).trans (PushoutI.of_comp_eq_base (φ:=diagram f g) true).symm
lemma diagram_injective {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∀ i, Function.Injective (diagram f g i) := by
  intro i; cases i; exact hf; exact hg
lemma left_injective {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (left f g) :=
  PushoutI.of_injective (diagram_injective hf hg) false
lemma right_injective {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (right f g) :=
  PushoutI.of_injective (diagram_injective hf hg) true

def targets (l : A →* K) (r : B →* K) : ∀ i, Family A B i →* K
  | false => l
  | true => r

def lift {f : H →* A} {g : H →* B} (l : A →* K) (r : B →* K)
    (h : l.comp f=r.comp g) : GroupOf f g →* K :=
  PushoutI.lift (targets l r) (l.comp f) (by intro i; cases i; rfl; exact h.symm)
@[simp] lemma lift_left {f : H →* A} {g : H →* B} (l : A →* K) (r : B →* K)
    (h : l.comp f=r.comp g) (a : A) : lift l r h (left f g a)=l a :=
  PushoutI.lift_of _ _ _ _
@[simp] lemma lift_right {f : H →* A} {g : H →* B} (l : A →* K) (r : B →* K)
    (h : l.comp f=r.comp g) (b : B) : lift l r h (right f g b)=r b :=
  PushoutI.lift_of _ _ _ _

lemma centralizer_right {f : H →* A} {g : H →* B}
    (hf : Function.Injective f) (hg : Function.Injective g) (q : B)
    (hq : ∀ b : B, b*q*b⁻¹∉g.range) (x : GroupOf f g)
    (hx : Commute x (right f g q)) : x∈(right f g).range :=
  AmalgamTools.centralizer_in_factor (diagram_injective hf hg) true q hq x hx
end ArtinCAT0.BinaryAmalgam

namespace ArtinCAT0.FreeTwo
open Monoid
abbrev Cyclic := Multiplicative ℤ
def maps (_ : Bool) : PUnit →* Cyclic := 1
abbrev GroupOf := PushoutI maps
def gen (i : Bool) : GroupOf := PushoutI.of i (Multiplicative.ofAdd (1 : ℤ))
lemma maps_injective (i : Bool) : Function.Injective (maps i) := fun _ _ _ => Subsingleton.elim _ _
lemma gen_ne_one (i : Bool) : gen i≠1 := by
  intro h
  have he := PushoutI.of_injective maps_injective i (h.trans (map_one _).symm)
  change Multiplicative.ofAdd (1 : ℤ)=Multiplicative.ofAdd 0 at he
  exact Int.one_ne_zero (Multiplicative.ofAdd.injective he)

def lift {K : Type*} [Group K] (q : Bool→K) : GroupOf →* K :=
  PushoutI.lift (fun i => zpowersHom K (q i)) 1 (by
    intro i
    ext x
    simp [maps])
@[simp] lemma lift_gen {K : Type*} [Group K] (q : Bool→K) (i : Bool) :
    lift q (gen i)=q i := by simp [lift,gen,zpowersHom_apply]

lemma common_centralizer (x : GroupOf) (hx : ∀ i, Commute x (gen i)) : x=1 := by
  have hmem (i : Bool) : x∈(PushoutI.of (φ:=maps) i).range := by
    apply AmalgamTools.centralizer_in_factor maps_injective i _ _ x (hx i)
    intro b
    rintro ⟨y,hy⟩
    have he : (1:ℤ)=0 := by
      have hh : Multiplicative.ofAdd (1:ℤ)=(1:Cyclic) := by
        simpa [maps,mul_comm,mul_left_comm] using hy.symm
      exact Multiplicative.ofAdd.injective hh
    exact Int.one_ne_zero he
  have hboth : x∈(PushoutI.of (φ:=maps) false).range ⊓ (PushoutI.of (φ:=maps) true).range :=
    ⟨hmem false,hmem true⟩
  rw [PushoutI.inf_of_range_eq_base_range maps_injective Bool.false_ne_true] at hboth
  obtain ⟨y,rfl⟩ := hboth
  have hy : y=1 := Subsingleton.elim _ _
  rw [hy,map_one]
end ArtinCAT0.FreeTwo
open scoped Classical
namespace ArtinCAT0

lemma blockLetter_injective (b : Fin 3) : Function.Injective (blockLetter b) := by
  intro i j he
  unfold blockLetter at he
  split_ifs at he <;> simp only [Fin.mk.injEq] at he <;> apply Fin.ext <;> omega

lemma blockLetter_private {b c : Fin 3} {i j : Fin 39} (hi : 2 ≤ i.val)
    (he : blockLetter b i=blockLetter c j) : b=c ∧ i=j := by
  unfold blockLetter at he
  split_ifs at he <;> simp only [Fin.mk.injEq] at he
  all_goals try omega

lemma blockLetter_nonsentinel (b : Fin 3) (i : Fin 39) :
    (blockLetter b i).val≠3 ∧ (blockLetter b i).val≠4 := by
  unfold blockLetter
  split_ifs <;> dsimp <;> omega

lemma adjacent_symm {s t : Letters} (h : Adjacent s t) : Adjacent t s := by
  obtain ⟨b,i,j,rfl,rfl,h⟩ := h
  exact ⟨b,j,i,rfl,rfl,h.symm⟩
lemma distant_symm {s t : Letters} (h : Distant s t) : Distant t s := by
  obtain ⟨b,i,j,rfl,rfl,h⟩ := h
  exact ⟨b,j,i,rfl,rfl,h.symm⟩
lemma sentinel_symm {s t : Letters} (h : Sentinel s t) : Sentinel t s := h.symm

lemma adjacent_not_distant {s t : Letters} (ha : Adjacent s t) : ¬Distant s t := by
  obtain ⟨b,i,j,rfl,rfl,hij⟩ := ha
  rintro ⟨c,k,l,hik,hjl,hkl⟩
  have hc : b=c := by
    rcases hkl with hkl|hlk
    · have hh := blockLetter_private (j:=j) (by omega : 2 ≤ l.val) hjl.symm
      exact hh.1.symm
    · have hh := blockLetter_private (j:=i) (by omega : 2 ≤ k.val) hik.symm
      exact hh.1.symm
  subst c
  have hik' := blockLetter_injective b hik
  have hjl' := blockLetter_injective b hjl
  subst k; subst l
  omega

lemma sentinel_not_adjacent {s t : Letters} (hs : Sentinel s t) : ¬Adjacent s t := by
  rintro ⟨b,i,j,rfl,rfl,_⟩
  have hi := blockLetter_nonsentinel b i
  have hj := blockLetter_nonsentinel b j
  rcases hs with ⟨h,_⟩|⟨h,_⟩ <;> omega

lemma explicitMatrix_symmetric (s t : Letters) : explicitMatrix s t=explicitMatrix t s := by
  have ha : Adjacent s t ↔ Adjacent t s := ⟨adjacent_symm,adjacent_symm⟩
  have hd : Distant s t ↔ Distant t s := ⟨distant_symm,distant_symm⟩
  have hs : Sentinel s t ↔ Sentinel t s := ⟨sentinel_symm,sentinel_symm⟩
  simp only [explicitMatrix,eq_comm,ha,hd,hs]

@[simp] lemma explicitMatrix_diagonal (s : Letters) : explicitMatrix s s=1 := by
  simp [explicitMatrix]

lemma explicitMatrix_values (s t : Letters) (h : s≠t) :
    explicitMatrix s t=2 ∨ explicitMatrix s t=3 ∨ explicitMatrix s t=⊤ := by
  unfold explicitMatrix
  simp only [ite_eq_right h]
  split_ifs <;> simp

lemma matrix_block_adjacent (b : Fin 3) (i j : Fin 39)
    (hij : i.val+1=j.val ∨ j.val+1=i.val) :
    explicitMatrix (blockLetter b i) (blockLetter b j)=3 := by
  have he : blockLetter b i≠blockLetter b j := fun he => by
    have := blockLetter_injective b he
    subst j
    omega
  have ha : Adjacent (blockLetter b i) (blockLetter b j) := ⟨b,i,j,rfl,rfl,hij⟩
  simp [explicitMatrix,he,ha]

lemma matrix_block_distant (b : Fin 3) (i j : Fin 39)
    (hij : i.val+2 ≤ j.val ∨ j.val+2 ≤ i.val) :
    explicitMatrix (blockLetter b i) (blockLetter b j)=2 := by
  have he : blockLetter b i≠blockLetter b j := fun he => by
    have := blockLetter_injective b he
    subst j
    omega
  have hd : Distant (blockLetter b i) (blockLetter b j) := ⟨b,i,j,rfl,rfl,hij⟩
  have hn : ¬Adjacent (blockLetter b i) (blockLetter b j) := fun ha => adjacent_not_distant ha hd
  simp [explicitMatrix,he,hn,hd]

lemma matrix_sentinel (s t : Letters) (hs : Sentinel s t) : explicitMatrix s t=2 := by
  have he : s≠t := by rintro rfl; rcases hs with ⟨h,ht⟩|⟨h,ht⟩ <;> omega
  simp [explicitMatrix,he,sentinel_not_adjacent hs,hs]

abbrev MainGroup := ArtinGroup explicitMatrix
abbrev mainGen (s : Letters) : MainGroup := PresentedGroup.of s

lemma artin_braid {S : Type*} (M : S→S→Label) (s t : S) (h : M s t=3) :
    PresentedGroup.of (rels:=artinRelators M) s * PresentedGroup.of t * PresentedGroup.of s =
      PresentedGroup.of t * PresentedGroup.of s * PresentedGroup.of t := by
  have hh := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels:=artinRelators M) ⟨s,t,3,h,rfl⟩
  simpa [alternating,PresentedGroup.of,map_mul,mul_assoc] using hh

lemma artin_commute {S : Type*} (M : S→S→Label) (s t : S) (h : M s t=2) :
    Commute (PresentedGroup.of (rels:=artinRelators M) s) (PresentedGroup.of t) := by
  have hh := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels:=artinRelators M) ⟨s,t,2,h,rfl⟩
  simpa [alternating,PresentedGroup.of,map_mul,Commute,SemiconjBy] using hh

section Lift
variable {H : Type*} [Group H]

def mainLift (v : Letters → H)
    (hb : ∀ s t, Adjacent s t → v s*v t*v s=v t*v s*v t)
    (hc : ∀ s t, Distant s t ∨ Sentinel s t → Commute (v s) (v t)) : MainGroup →* H :=
  PresentedGroup.toGroup (f:=v) (by
    rintro r ⟨s,t,n,hn,rfl⟩
    simp only [map_mul,map_inv,mul_inv_eq_one]
    unfold explicitMatrix at hn
    split_ifs at hn with he ha hd
    · have hn' : n=1 := by exact_mod_cast hn.symm
      subst n; subst t
      rfl
    · have hn' : n=3 := by exact_mod_cast hn.symm
      subst n
      simpa [alternating,map_mul,mul_assoc] using hb s t ha
    · have hn' : n=2 := by exact_mod_cast hn.symm
      subst n
      simpa [alternating,map_mul] using (hc s t hd).eq
    · exact False.elim (WithTop.top_ne_coe hn))

@[simp] lemma mainLift_gen (v : Letters → H) (hb hc) (s : Letters) :
    mainLift v hb hc (mainGen s)=v s := PresentedGroup.toGroup.of _

end Lift
end ArtinCAT0
open scoped Classical
namespace ArtinCAT0.Assembly
open BinaryAmalgam

abbrev inc := initialBraidInclusion 39 (by norm_num)
abbrev A₁ := GroupOf (trianglePair 0) inc
def t₁ : TriangleGroup →* A₁ := left (trianglePair 0) inc
abbrev A₂ := GroupOf (t₁.comp (trianglePair 1)) inc
def t₂ : TriangleGroup →* A₂ := (left (t₁.comp (trianglePair 1)) inc).comp t₁
abbrev A₃ := GroupOf (t₂.comp (trianglePair 2)) inc
def t₃ : TriangleGroup →* A₃ := (left (t₂.comp (trianglePair 2)) inc).comp t₂

lemma inc_injective : Function.Injective inc := initialBraidInclusion_injective 39 (by norm_num)
lemma t₁_injective : Function.Injective t₁ := left_injective (trianglePair_injective 0) inc_injective
lemma t₂_injective : Function.Injective t₂ := by
  intro a b h
  apply t₁_injective
  exact left_injective (f:=t₁.comp (trianglePair 1)) (g:=inc)
    (t₁_injective.comp (trianglePair_injective 1)) inc_injective h
lemma t₃_injective : Function.Injective t₃ := by
  intro a b h
  apply t₂_injective
  exact left_injective (f:=t₂.comp (trianglePair 2)) (g:=inc)
    (t₂_injective.comp (trianglePair_injective 2)) inc_injective h

def block₀ : BraidGroup 39 →* A₃ :=
  (left (t₂.comp (trianglePair 2)) inc).comp
    ((left (t₁.comp (trianglePair 1)) inc).comp (right (trianglePair 0) inc))
def block₁ : BraidGroup 39 →* A₃ :=
  (left (t₂.comp (trianglePair 2)) inc).comp (right (t₁.comp (trianglePair 1)) inc)
def block₂ : BraidGroup 39 →* A₃ := right (t₂.comp (trianglePair 2)) inc

def block (b : Fin 3) : BraidGroup 39 →* A₃ := ![block₀,block₁,block₂] b
lemma block_agree (b : Fin 3) : (block b).comp inc=t₃.comp (trianglePair b) := by
  apply MonoidHom.ext
  intro x
  fin_cases b
  · exact congrArg (fun y : A₁ => left (t₂.comp (trianglePair 2)) inc
      (left (t₁.comp (trianglePair 1)) inc y))
      (DFunLike.congr_fun (agree (trianglePair 0) inc) x).symm
  · exact congrArg (left (t₂.comp (trianglePair 2)) inc)
      (DFunLike.congr_fun (agree (t₁.comp (trianglePair 1)) inc) x).symm
  · exact (DFunLike.congr_fun (agree (t₂.comp (trianglePair 2)) inc) x).symm

abbrev Product := TriangleGroup × FreeTwo.GroupOf
def productT : TriangleGroup →* Product := (MonoidHom.id _).prod 1
lemma productT_injective : Function.Injective productT := by
  intro a b h
  exact congrArg Prod.fst h
abbrev Model := GroupOf t₃ productT
def triangle : TriangleGroup →* Model := (left t₃ productT).comp t₃
def braidBlock (b : Fin 3) : BraidGroup 39 →* Model := (left t₃ productT).comp (block b)
def sentinel (i : Bool) : Model := right t₃ productT (1,FreeTwo.gen i)
lemma triangle_injective : Function.Injective triangle :=
  (left_injective t₃_injective productT_injective).comp t₃_injective
lemma triangle_eq_right : triangle=(right t₃ productT).comp productT := agree _ _
lemma braidBlock_agree (b : Fin 3) : (braidBlock b).comp inc=triangle.comp (trianglePair b) := by
  simp only [braidBlock,triangle,MonoidHom.comp_assoc,block_agree]

lemma product_conjugate_not_base (i : Bool) (b : Product) :
    b*(1,FreeTwo.gen i)*b⁻¹∉productT.range := by
  rintro ⟨a,ha⟩
  have he : b.2*FreeTwo.gen i*b.2⁻¹=1 := (congrArg Prod.snd ha).symm
  have hh : FreeTwo.gen i=1 := by
    have := congrArg (fun x => b.2⁻¹*x*b.2) he
    simpa [mul_assoc] using this
  exact FreeTwo.gen_ne_one i hh

lemma common_centralizer (g : Model) (hg : ∀ i, Commute g (sentinel i)) : g∈triangle.range := by
  obtain ⟨b,rfl⟩ := centralizer_right t₃_injective productT_injective (1,FreeTwo.gen false)
    (product_conjugate_not_base false) g (hg false)
  have hb (i : Bool) : Commute b (1,FreeTwo.gen i) := by
    apply (right_injective t₃_injective productT_injective)
    simpa only [map_mul,sentinel] using (hg i).eq
  have hf : b.2=1 := FreeTwo.common_centralizer b.2 (fun i => (hb i).map (MonoidHom.snd _ _))
  refine ⟨b.1,?_⟩
  rw [triangle_eq_right]
  change right t₃ productT (b.1,1)=right t₃ productT b
  rw [← hf]

def corner (i : Fin 3) : Letters := ⟨i.val,by omega⟩
@[simp] lemma blockLetter_zero (b : Fin 3) : blockLetter b 0=corner b := by
  simp [blockLetter,corner]
@[simp] lemma blockLetter_one (b : Fin 3) : blockLetter b 1=corner (b+1) := by
  apply Fin.ext
  simp [blockLetter,corner,Fin.add_def]

lemma braidBlock_zero (b : Fin 3) : braidBlock b (braidGen 39 0)=triangle (triangleGen b) := by
  have h := DFunLike.congr_fun (braidBlock_agree b) (braidGen 2 0)
  simpa [inc,initialBraidInclusion,trianglePair,braidGen] using h
lemma braidBlock_one (b : Fin 3) : braidBlock b (braidGen 39 1)=triangle (triangleGen (b+1)) := by
  have h := DFunLike.congr_fun (braidBlock_agree b) (braidGen 2 1)
  simpa [inc,initialBraidInclusion,trianglePair,braidGen] using h

def letter (s : Letters) : Model :=
  if hs : s.val<3 then triangle (triangleGen ⟨s.val,hs⟩)
  else if s.val=3 then sentinel false
  else if s.val=4 then sentinel true
  else braidBlock ⟨(s.val-5)/37,by omega⟩ (braidGen 39 ((s.val-5)%37+2))
@[simp] lemma letter_corner (i : Fin 3) : letter (corner i)=triangle (triangleGen i) := by
  simp [letter,corner,i.isLt]
@[simp] lemma letter_three : letter 3=sentinel false := by simp [letter]
@[simp] lemma letter_four : letter 4=sentinel true := by simp [letter]
lemma letter_block (b : Fin 3) (i : Fin 39) : letter (blockLetter b i)=braidBlock b (braidGen 39 i.val) := by
  rcases lt_or_ge i.val 2 with hi|hi
  · have he : i=0 ∨ i=1 := by omega
    rcases he with rfl|rfl
    · simpa only [Fin.val_zero,blockLetter_zero,letter_corner] using (braidBlock_zero b).symm
    · simpa only [Fin.val_one,blockLetter_one,letter_corner] using (braidBlock_one b).symm
  · have h₀ : i.val≠0 := by omega
    have h₁ : i.val≠1 := by omega
    have hs : (blockLetter b i).val=5+37*b.val+(i.val-2) := by simp [blockLetter,h₀,h₁]
    have hsmall : ¬(blockLetter b i).val<3 := by omega
    have h3 : (blockLetter b i).val≠3 := by omega
    have h4 : (blockLetter b i).val≠4 := by omega
    have hb : ((blockLetter b i).val-5)/37=b.val := by omega
    have hj : ((blockLetter b i).val-5)%37+2=i.val := by omega
    simp only [letter,dite_eq_right hsmall,ite_eq_right h3,ite_eq_right h4,hj]
    congr 2
    exact Fin.ext hb

lemma letter_braid (s t : Letters) (h : Adjacent s t) :
    letter s*letter t*letter s=letter t*letter s*letter t := by
  obtain ⟨b,i,j,rfl,rfl,h⟩ := h
  rw [letter_block,letter_block]
  rcases h with h|h
  · have he := congrArg (braidBlock b) (braidGroup_relation 39 i.val (by omega))
    simpa only [map_mul,h] using he
  · have he := congrArg (braidBlock b) (braidGroup_relation 39 j.val (by omega))
    simpa only [map_mul,h] using he.symm

lemma triangle_sentinel_commute (t : TriangleGroup) (i : Bool) : Commute (triangle t) (sentinel i) := by
  rw [triangle_eq_right]
  apply Commute.map (f:=right t₃ productT)
  change Commute (t,1) (1,FreeTwo.gen i)
  change (t,1)*(1,FreeTwo.gen i)=(1,FreeTwo.gen i)*(t,1)
  simp

lemma letter_commute (s t : Letters) (h : Distant s t ∨ Sentinel s t) : Commute (letter s) (letter t) := by
  rcases h with h|h
  · obtain ⟨b,i,j,rfl,rfl,h⟩ := h
    rw [letter_block,letter_block]
    rcases h with h|h
    · exact (braidGroup_commute 39 i.val j.val h j.isLt).map (braidBlock b)
    · exact ((braidGroup_commute 39 j.val i.val h i.isLt).map (braidBlock b)).symm
  · have hh (s t : Letters) (hs : s.val=3 ∨ s.val=4) (ht : t.val<3) :
        Commute (letter s) (letter t) := by
      have ht' : t=corner ⟨t.val,ht⟩ := rfl
      rw [ht',letter_corner]
      rcases hs with hs|hs
      · have hs' : s=3 := Fin.ext hs
        rw [hs',letter_three]
        exact (triangle_sentinel_commute _ _).symm
      · have hs' : s=4 := Fin.ext hs
        rw [hs',letter_four]
        exact (triangle_sentinel_commute _ _).symm
    rcases h with ⟨hs,ht⟩|⟨ht,hs⟩
    · exact hh s t hs ht
    · exact (hh t s ht hs).symm

def toModel : MainGroup →* Model := mainLift letter letter_braid letter_commute
@[simp] lemma toModel_gen (s : Letters) : toModel (mainGen s)=letter s := mainLift_gen _ _ _ _

def triangleMain : TriangleGroup →* MainGroup := triangleLift (fun i => mainGen (corner i)) (by
  intro i
  have h := matrix_block_adjacent i 0 1 (by decide)
  rw [blockLetter_zero,blockLetter_one] at h
  exact artin_braid _ _ _ h)
@[simp] lemma triangleMain_gen (i : Fin 3) : triangleMain (triangleGen i)=mainGen (corner i) :=
  triangleLift_gen _ _ _

def blockMain (b : Fin 3) : BraidGroup 39 →* MainGroup := braidLift (fun i => mainGen (blockLetter b i))
  (fun i hi => artin_braid _ _ _ (matrix_block_adjacent b ⟨i,by omega⟩ ⟨i+1,hi⟩ (Or.inl rfl)))
  (fun i j hij => artin_commute _ _ _ (matrix_block_distant b i j (Or.inl hij)))
@[simp] lemma blockMain_gen (b : Fin 3) (i : ℕ) (hi : i<39) :
    blockMain b (braidGen 39 i)=mainGen (blockLetter b ⟨i,hi⟩) := braidLift_gen _ _ _ _ hi
lemma blockMain_agree (b : Fin 3) : (blockMain b).comp inc=triangleMain.comp (trianglePair b) := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp [inc,initialBraidInclusion,trianglePair,braidGen,blockMain]

def sentinelMain (i : Bool) : MainGroup := if i then mainGen 4 else mainGen 3
lemma triangleMain_commute (t : TriangleGroup) : ∀ i, Commute (triangleMain t) (sentinelMain i) := by
  let C := (tupleCentralizer sentinelMain).comap triangleMain
  have hgen (k : Fin 3) : PresentedGroup.of (rels:=triangleRelators) k∈C := by
    change ∀ i, Commute (triangleMain (triangleGen k)) (sentinelMain i)
    intro i
    rw [triangleMain_gen]
    cases i
    · exact artin_commute _ _ _ (matrix_sentinel _ _ (Or.inr ⟨Or.inl rfl,k.isLt⟩))
    · exact artin_commute _ _ _ (matrix_sentinel _ _ (Or.inr ⟨Or.inr rfl,k.isLt⟩))
  exact PresentedGroup.generated_by triangleRelators C hgen t

def freeMain : FreeTwo.GroupOf →* MainGroup := FreeTwo.lift sentinelMain
@[simp] lemma freeMain_gen (i : Bool) : freeMain (FreeTwo.gen i)=sentinelMain i := FreeTwo.lift_gen _ _
lemma factors_commute (t : TriangleGroup) (f : FreeTwo.GroupOf) : Commute (triangleMain t) (freeMain f) := by
  apply Monoid.PushoutI.induction_on f
  · intro i g
    simpa [freeMain,FreeTwo.lift,zpowersHom_apply] using (triangleMain_commute t i).zpow_right g.toAdd
  · intro g
    simp [freeMain,FreeTwo.lift]
  · intro a b ha hb
    simpa only [map_mul] using ha.mul_right hb

def productMain : Product →* MainGroup := triangleMain.noncommCoprod freeMain factors_commute
@[simp] lemma productMain_apply (t : TriangleGroup) (f : FreeTwo.GroupOf) :
    productMain (t,f)=triangleMain t*freeMain f := rfl
lemma productMain_triangle : productMain.comp productT=triangleMain := by
  apply MonoidHom.ext
  intro x
  simp [productT]

def back₁ : A₁ →* MainGroup := lift triangleMain (blockMain 0) (blockMain_agree 0).symm
lemma back₁_triangle : back₁.comp t₁=triangleMain := by
  apply MonoidHom.ext
  intro x
  simp [back₁,t₁]
def back₂ : A₂ →* MainGroup := lift back₁ (blockMain 1) (by
  rw [← MonoidHom.comp_assoc,back₁_triangle]
  exact (blockMain_agree 1).symm)
lemma back₂_triangle : back₂.comp t₂=triangleMain := by
  apply MonoidHom.ext
  intro x
  change back₂ (left (t₁.comp (trianglePair 1)) inc (t₁ x))=triangleMain x
  rw [back₂,lift_left]
  exact DFunLike.congr_fun back₁_triangle x
def back₃ : A₃ →* MainGroup := lift back₂ (blockMain 2) (by
  rw [← MonoidHom.comp_assoc,back₂_triangle]
  exact (blockMain_agree 2).symm)
lemma back₃_triangle : back₃.comp t₃=triangleMain := by
  apply MonoidHom.ext
  intro x
  change back₃ (left (t₂.comp (trianglePair 2)) inc (t₂ x))=triangleMain x
  rw [back₃,lift_left]
  exact DFunLike.congr_fun back₂_triangle x
lemma back₃_block (b : Fin 3) : back₃.comp (block b)=blockMain b := by
  apply MonoidHom.ext
  intro x
  fin_cases b <;> simp [block,block₀,block₁,block₂,back₃,back₂,back₁]

def fromModel : Model →* MainGroup := lift back₃ productMain (by
  rw [back₃_triangle,productMain_triangle])
lemma fromModel_triangle : fromModel.comp triangle=triangleMain := by
  apply MonoidHom.ext
  intro x
  simp only [triangle,MonoidHom.comp_apply,fromModel,lift_left]
  exact DFunLike.congr_fun back₃_triangle x
lemma fromModel_block (b : Fin 3) : fromModel.comp (braidBlock b)=blockMain b := by
  apply MonoidHom.ext
  intro x
  simp only [braidBlock,MonoidHom.comp_apply,fromModel,lift_left]
  exact DFunLike.congr_fun (back₃_block b) x
@[simp] lemma fromModel_sentinel (i : Bool) : fromModel (sentinel i)=sentinelMain i := by
  simp [fromModel,sentinel]

lemma letter_cover (s : Letters) : s=3 ∨ s=4 ∨ ∃ b i, s=blockLetter b i := by
  by_cases h3 : s=3
  · exact Or.inl h3
  by_cases h4 : s=4
  · exact Or.inr (Or.inl h4)
  right; right
  by_cases hs : s.val<3
  · exact ⟨⟨s.val,hs⟩,0,by rw [blockLetter_zero]; rfl⟩
  have hval : 5 ≤ s.val := by
    have hh3 : s.val≠3 := fun h => h3 (Fin.ext h)
    have hh4 : s.val≠4 := fun h => h4 (Fin.ext h)
    omega
  refine ⟨⟨(s.val-5)/37,by omega⟩,⟨(s.val-5)%37+2,by omega⟩,?_⟩
  apply Fin.ext
  simp only [blockLetter]
  split_ifs <;> dsimp at * <;> omega

lemma fromModel_letter (s : Letters) : fromModel (letter s)=mainGen s := by
  rcases letter_cover s with rfl|rfl|⟨b,i,rfl⟩
  · simp [sentinelMain]
  · simp [sentinelMain]
  · rw [letter_block]
    change (fromModel.comp (braidBlock b)) (braidGen 39 i.val)=_
    rw [fromModel_block,blockMain_gen b i.val i.isLt]
lemma fromModel_toModel : fromModel.comp toModel=MonoidHom.id MainGroup := by
  apply PresentedGroup.ext
  intro s
  change fromModel (toModel (mainGen s))=mainGen s
  rw [toModel_gen,fromModel_letter]
lemma toModel_injective : Function.Injective toModel := by
  apply Function.Injective.of_comp (f:=fromModel)
  rw [← MonoidHom.coe_comp,fromModel_toModel]
  exact Function.injective_id
lemma toModel_triangleMain : toModel.comp triangleMain=triangle := by
  apply PresentedGroup.ext
  intro i
  change toModel (triangleMain (triangleGen i))=triangle (triangleGen i)
  rw [triangleMain_gen,toModel_gen,letter_corner]
lemma triangleMain_injective : Function.Injective triangleMain := by
  apply Function.Injective.of_comp (f:=toModel)
  rw [← MonoidHom.coe_comp,toModel_triangleMain]
  exact triangle_injective
@[simp] lemma toModel_sentinelMain (i : Bool) : toModel (sentinelMain i)=sentinel i := by
  cases i <;> simp [sentinelMain]
lemma main_common_centralizer (g : MainGroup) (hg : ∀ i, Commute g (sentinelMain i)) : g∈triangleMain.range := by
  have hh (i : Bool) : Commute (toModel g) (sentinel i) := by
    simpa only [toModel_sentinelMain] using (hg i).map toModel
  obtain ⟨t,ht⟩ := common_centralizer (toModel g) hh
  refine ⟨t,?_⟩
  apply toModel_injective
  change (toModel.comp triangleMain) t=toModel g
  rw [toModel_triangleMain]
  exact ht

def triangleCentralizer : TriangleGroup →* tupleCentralizer sentinelMain :=
  triangleMain.codRestrict _ triangleMain_commute
lemma triangleCentralizer_bijective : Function.Bijective triangleCentralizer := by
  constructor
  · intro a b h
    apply triangleMain_injective
    exact congrArg Subtype.val h
  · intro g
    obtain ⟨t,ht⟩ := main_common_centralizer g.val g.property
    exact ⟨t,Subtype.ext ht⟩
end ArtinCAT0.Assembly
namespace ArtinCAT0
variable {G H X : Type*} [Group G] [Group H] [MetricSpace X] [MulAction G X]

lemma geometric_compHom (f : H →* G) (hf : Function.Bijective f) (hG : GeometricAction G X) :
    let := MulAction.compHom X f
    GeometricAction H X := by
  let := MulAction.compHom X f
  refine ⟨hG.1,fun h => hG.2.1 (f h),?_,?_⟩
  · intro K hK
    change (f ⁻¹' {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}).Finite
    exact (hG.2.2.1 K hK).preimage (fun _ _ _ _ h => hf.1 h)
  · obtain ⟨K,hK,hcov⟩ := hG.2.2.2
    refine ⟨K,hK,?_⟩
    intro x
    obtain ⟨g,k,hk,hgk⟩ := hcov x
    obtain ⟨h,rfl⟩ := hf.2 g
    exact ⟨h,k,hk,hgk⟩

lemma stableLength_compHom (f : H →* G) (x : X) (h : H) :
    let := MulAction.compHom X f
    stableLengthAt x h=stableLengthAt x (f h) := by
  let := MulAction.compHom X f
  simp only [stableLengthAt,MulAction.compHom_smul_def,map_pow]

lemma generator_square_positive [ProperSpace X] [Nonempty X]
    {S : Type*} (M : S→S→Label) [MulAction (ArtinGroup M) X]
    (hG : GeometricAction (ArtinGroup M) X) (x : X) (s : S) :
    0<stableLengthAt x ((PresentedGroup.of (rels:=artinRelators M) s)^2) := by
  have hp : 0<stableLengthAt x (PresentedGroup.of (rels:=artinRelators M) s) := by
    apply lt_of_le_of_ne (stableLength_nonneg hG.2.1 x _)
    intro h
    exact artin_generator_infinite_order M s ((stableLength_eq_zero_iff_finiteOrder hG x _).mp h.symm)
  rw [stableLength_pow hG.2.1]
  positivity
end ArtinCAT0

end OAI
end
end

section
section
namespace OAI

open scoped Classical
namespace ArtinCAT0
namespace Assembly
@[simp] lemma blockMain_zero (i : Fin 3) : blockMain i (braidGen 39 0)=mainGen (corner i) := by
  have h := blockMain_gen i 0 (by norm_num)
  change blockMain i (braidGen 39 0)=mainGen (blockLetter i 0) at h
  simpa only [blockLetter_zero] using h
@[simp] lemma blockMain_one (i : Fin 3) : blockMain i (braidGen 39 1)=mainGen (corner (i+1)) := by
  have h := blockMain_gen i 1 (by norm_num)
  change blockMain i (braidGen 39 1)=mainGen (blockLetter i 1) at h
  simpa only [blockLetter_one] using h

lemma blockMain_relations (i : Fin 3) : BraidRelations 39 (fun n => blockMain i (braidGen 39 n)) := by
  constructor
  · intro j hj
    simpa only [map_mul] using congrArg (blockMain i) ((braidGroup_relations 39).1 j hj)
  · intro j k hj hk hjk
    exact ((braidGroup_relations 39).2 j k hj hk hjk).map (blockMain i)

/-- The literal 116-generator presentation has no geometric CAT(0) action. -/
theorem not_geometric (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
    [MulAction MainGroup X] : ¬GeometricAction MainGroup X := by
  classical
  intro hG
  obtain ⟨A,hA,hY⟩ := exists_sublevel_nonempty (X:=X) sentinelMain
  let Y := displacementSublevel (X:=X) sentinelMain A
  let : Nonempty Y := hY
  let : ProperSpace Y := sublevel_properSpace hG.2.1 sentinelMain A
  let := sublevelAction hG.2.1 sentinelMain A
  have hC := geometric_tupleCentralizer hG sentinelMain A hA
  let := MulAction.compHom Y triangleCentralizer
  have hT : GeometricAction TriangleGroup Y := geometric_compHom triangleCentralizer triangleCentralizer_bijective hC
  let y : Y := Classical.choice inferInstance
  have hl (g : TriangleGroup) : stableLengthAt y g=stableLengthAt y.val (triangleMain g) := by
    rw [stableLength_compHom triangleCentralizer]
    exact sublevelAction_stableLength hG.2.1 sentinelMain A y (triangleCentralizer g)
  apply SixSector.no_strict_ratios hT y
  intro i
  have hp : 0<stableLengthAt y.val ((blockMain i (braidGen 39 0))^2) := by
    rw [blockMain_zero]
    exact generator_square_positive explicitMatrix hG y.val (corner i)
  have hr := (braid_forty_ratio hG y.val (blockMain_relations i) hp).2.1
  simpa only [hl,triangleH,map_pow,map_mul,triangleMain_gen,blockMain_zero,blockMain_one] using hr
end Assembly


theorem main_oai :
    (∀ s t : Letters, explicitMatrix s t = explicitMatrix t s) ∧
    (∀ s : Letters, explicitMatrix s s = 1) ∧
    (∀ s t : Letters, s ≠ t →
      explicitMatrix s t = 2 ∨ explicitMatrix s t = 3 ∨ explicitMatrix s t = ⊤) ∧
    (∀ (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
      [MulAction (ArtinGroup explicitMatrix) X],
      ¬ GeometricAction (ArtinGroup explicitMatrix) X) := by
  exact ⟨explicitMatrix_symmetric,explicitMatrix_diagonal,explicitMatrix_values,Assembly.not_geometric⟩
end ArtinCAT0

end OAI
end
end

theorem solution : type_of% @OAI.ArtinCAT0.main_oai := @OAI.ArtinCAT0.main_oai
