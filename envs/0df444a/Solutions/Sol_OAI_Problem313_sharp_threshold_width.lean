-- Prove2me | solution 1 for OAI.Problem313.sharp_threshold_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T12:31:50.376386+00:00
-- url     : https://prove2.me/submissions/70ee9747-0880-4cdf-8d7d-640230f88257

import Mathlib
import Definitions.Def_SharpThreshold

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

universe u v w

section
section
namespace OAI

noncomputable section

namespace Problem313

def graphVariance {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    graphWeight p x * (boolReal (f x) - graphMean p f) ^ 2)

def edgeInfluence {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (e : GraphEdge n) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    if f (Function.update x e true) ≠ f (Function.update x e false)
    then graphWeight p x else 0)

def totalInfluence {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun e : GraphEdge n => edgeInfluence p f e)

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- A permutation of a block, extended by the identity away from the block. -/
def extendBlockPerm {α : Type u} [DecidableEq α] (B : Finset α)
    (σ : Equiv.Perm B) : Equiv.Perm α :=
  σ.extendDomain (Equiv.refl B)

@[simp]
theorem extendBlockPerm_apply_mem {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : B) :
    extendBlockPerm B σ x = (σ x : α) := by
  exact Equiv.Perm.extendDomain_apply_image σ (Equiv.refl B) x

@[simp]
theorem extendBlockPerm_apply_notMem {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : α) (hx : x ∉ B) :
    extendBlockPerm B σ x = x := by
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.refl B) hx

/-- Equal-sized subsets of a block can be mapped to one another while fixing its complement. -/
theorem exists_blockPerm_map {α : Type u} [DecidableEq α]
    (B s t : Finset α) (hs : s ⊆ B) (ht : t ⊆ B) (hc : s.card = t.card) :
    ∃ σ : Equiv.Perm B, s.map (extendBlockPerm B σ).toEmbedding = t := by
  classical
  have hs' : s.filter (· ∈ B) = s := Finset.filter_true_of_mem (fun _ hx => hs hx)
  have ht' : t.filter (· ∈ B) = t := Finset.filter_true_of_mem (fun _ hx => ht hx)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (s.subtype (· ∈ B)) (t.subtype (· ∈ B)) (by simpa [hs', ht'] using hc)
  refine ⟨σ, ?_⟩
  have hmap := congrArg (fun u : Finset B => u.map (Function.Embedding.subtype _)) hσ
  rw [Finset.subtype_map, ht'] at hmap
  rw [← Finset.subtype_map_of_mem (fun _ hx => hs hx)]
  simp only [Finset.map_map] at *
  convert hmap using 1
  congr 1
  ext x
  simp

/-- A block permutation fixes any finite set disjoint from the block. -/
theorem extendBlockPerm_map_disjoint {α : Type u} [DecidableEq α]
    (B s : Finset α) (σ : Equiv.Perm B) (hs : Disjoint s B) :
    s.map (extendBlockPerm B σ).toEmbedding = s := by
  classical
  have hfix : ∀ x ∈ s, extendBlockPerm B σ x = x := fun x hx =>
    extendBlockPerm_apply_notMem B σ x (Finset.disjoint_left.mp hs hx)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    change extendBlockPerm B σ y = x at hxy
    rw [hfix y hy] at hxy
    exact hxy ▸ hy
  · intro hx
    exact Finset.mem_map.mpr ⟨x, hx, hfix x hx⟩

/-- Equal-sized finite sets with the same exterior part are in the same block orbit. -/
theorem exists_blockPerm_map_of_sdiff_eq {α : Type u} [DecidableEq α]
    (B s t : Finset α) (hc : s.card = t.card) (hout : s \ B = t \ B) :
    ∃ σ : Equiv.Perm B, s.map (extendBlockPerm B σ).toEmbedding = t := by
  classical
  have hci : (s ∩ B).card = (t ∩ B).card := by
    have hs := Finset.card_sdiff_add_card_inter s B
    have ht := Finset.card_sdiff_add_card_inter t B
    rw [hout, hc] at hs
    omega
  obtain ⟨σ, hσ⟩ := exists_blockPerm_map B (s ∩ B) (t ∩ B)
    Finset.inter_subset_right Finset.inter_subset_right hci
  refine ⟨σ, ?_⟩
  have hs : s = (s ∩ B) ∪ (s \ B) := by ext x; simp; tauto
  calc
    s.map (extendBlockPerm B σ).toEmbedding =
        ((s ∩ B) ∪ (s \ B)).map (extendBlockPerm B σ).toEmbedding := congrArg _ hs
    _ = (t ∩ B) ∪ (t \ B) := by
      rw [Finset.map_union, hσ, extendBlockPerm_map_disjoint B (s \ B) σ
        Finset.sdiff_disjoint, hout]
    _ = t := by ext x; simp; tauto

/-- Edge transport preserving the vertices outside the selected block. -/
theorem exists_blockPerm_permEdge {n : ℕ} (B : Finset (Fin n))
    (e e' : GraphEdge n) (hout : e.1 \ B = e'.1 \ B) :
    ∃ σ : Equiv.Perm B, permEdge (extendBlockPerm B σ) e = e' := by
  obtain ⟨σ, hσ⟩ := exists_blockPerm_map_of_sdiff_eq B e.1 e'.1
    (e.2.trans e'.2.symm) hout
  exact ⟨σ, Subtype.ext hσ⟩

/-- Every edge not touching the block is fixed pointwise by the block action. -/
theorem permEdge_extendBlockPerm_of_disjoint {n : ℕ} (B : Finset (Fin n))
    (σ : Equiv.Perm B) (e : GraphEdge n) (he : Disjoint e.1 B) :
    permEdge (extendBlockPerm B σ) e = e := by
  exact Subtype.ext (extendBlockPerm_map_disjoint B e.1 σ he)

@[simp]
theorem extendBlockPerm_mem_iff {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : α) :
    extendBlockPerm B σ x ∈ B ↔ x ∈ B := by
  by_cases hx : x ∈ B
  · have h := extendBlockPerm_apply_mem B σ ⟨x, hx⟩
    rw [h]
    exact iff_of_true (σ ⟨x, hx⟩).2 hx
  · simp [extendBlockPerm_apply_notMem B σ x hx, hx]

@[simp]
theorem extendBlockPerm_map_block {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) :
    B.map (extendBlockPerm B σ).toEmbedding = B := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (extendBlockPerm_mem_iff B σ y).mpr hy
  · simp

/-- Block-supported permutations leave the exterior part of every finite set unchanged. -/
theorem extendBlockPerm_sdiff {α : Type u} [DecidableEq α]
    (B s : Finset α) (σ : Equiv.Perm B) :
    s.map (extendBlockPerm B σ).toEmbedding \ B = s \ B := by
  calc
    s.map (extendBlockPerm B σ).toEmbedding \ B =
        (s \ B).map (extendBlockPerm B σ).toEmbedding := by
      rw [Finset.map_sdiff, extendBlockPerm_map_block]
    _ = s \ B := extendBlockPerm_map_disjoint B (s \ B) σ Finset.sdiff_disjoint

/-- Two graph edges belong to the same block orbit exactly when their exterior vertices agree. -/
theorem exists_blockPerm_permEdge_iff {n : ℕ} (B : Finset (Fin n))
    (e e' : GraphEdge n) :
    (∃ σ : Equiv.Perm B, permEdge (extendBlockPerm B σ) e = e') ↔
      e.1 \ B = e'.1 \ B := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact (extendBlockPerm_sdiff B e.1 σ).symm
  · exact exists_blockPerm_permEdge B e e'

@[simp]
theorem extendBlockPerm_symm {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) :
    (extendBlockPerm B σ).symm = extendBlockPerm B σ.symm := by
  exact Equiv.Perm.extendDomain_symm σ (Equiv.refl B)

/-- Relabeling inside the block leaves each exterior configuration coordinate unchanged. -/
theorem permuteConfig_extendBlockPerm_apply_of_disjoint {n : ℕ}
    (B : Finset (Fin n)) (σ : Equiv.Perm B) (x : GraphConfig n)
    (e : GraphEdge n) (he : Disjoint e.1 B) :
    permuteConfig (extendBlockPerm B σ) x e = x e := by
  rw [permuteConfig, extendBlockPerm_symm,
    permEdge_extendBlockPerm_of_disjoint B σ.symm e he]

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

theorem half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor := Nat.sub_one_lt_floor x
  linarith

/-- Elementary size estimates for the square-root vertex block. -/
theorem sqrt_block_size_bounds (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    3 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ ∧
      ⌊Real.sqrt (n : ℝ)⌋₊ ≤ n ∧
      Real.sqrt (n : ℝ) / 2 ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnlarge : 17 ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hsqrt : 4 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).2 (by linarith)
  refine ⟨Nat.le_floor (by norm_num; linarith), ?_, half_le_nat_floor (by linarith)⟩
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

/-- The square-root block retains at least one third of the original logarithm. -/
theorem log_sqrt_block_lower (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) / 3 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hhalf := (sqrt_block_size_bounds n hn ht).2.2
  have hlog := Real.log_le_log (by positivity : 0 < Real.sqrt (n : ℝ) / 2) hhalf
  rw [Real.log_div (ne_of_gt hsqrtpos) (by norm_num),
    Real.log_sqrt (le_of_lt hnpos)] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

/-- Pair-inclusion correction for the square-root-sized uniform block. -/
theorem sqrt_block_pair_ratio (n : ℕ) (hn : 2 ≤ n) :
    ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1) ≤
      1 / Real.sqrt (n : ℝ) := by
  have hnreal : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtone : 1 ≤ Real.sqrt (n : ℝ) :=
    (Real.le_sqrt (by norm_num) (le_of_lt hnpos)).2 (by linarith)
  have hfloor := Nat.floor_le (Real.sqrt_nonneg (n : ℝ))
  have hprod := mul_le_mul_of_nonneg_right hfloor (le_of_lt hsqrtpos)
  have hsquare := Real.sq_sqrt (le_of_lt hnpos)
  apply (div_le_div_iff₀ (by linarith : 0 < (n : ℝ) - 1) hsqrtpos).2
  nlinarith

/-- A coarse exponential estimate sufficient for the block-capture union bound. -/
theorem block_capture_exp_lower (t : ℝ) (ht : 16 ≤ t) :
    2 * t ^ 2 ≤ Real.exp (t / 2) := by
  have htpos : 0 ≤ t := by linarith
  have hsq : 16 * t ≤ t ^ 2 := by
    nlinarith [mul_nonneg htpos (sub_nonneg.mpr ht)]
  have hcube : 256 * t ≤ t ^ 3 := by
    calc
      256 * t ≤ 16 * t ^ 2 := by linarith
      _ ≤ t * t ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
      _ = t ^ 3 := by ring
  have hexp := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ t / 4) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  have hlower : (17 / 12 : ℝ) * t ≤ Real.exp (t / 4) := by
    nlinarith
  have hsquare : ((17 / 12 : ℝ) * t) ^ 2 ≤ (Real.exp (t / 4)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlower 2
  have hid : Real.exp (t / 2) = (Real.exp (t / 4)) ^ 2 := by
    rw [show t / 2 = t / 4 + t / 4 by ring, Real.exp_add]
    ring
  rw [hid]
  nlinarith [sq_nonneg t]

theorem block_capture_decay (t : ℝ) (ht : 16 ≤ t) :
    t ^ 2 * Real.exp (-t / 2) ≤ (1 / 2 : ℝ) := by
  rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg,
    ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos (t / 2))).2
  have := block_capture_exp_lower t ht
  linarith

theorem log_square_div_sqrt_le_half (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) ≤ (1 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h := block_capture_exp_lower (Real.log (n : ℝ)) ht
  rw [Real.exp_half, Real.exp_log hnpos] at h
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnpos)).2
  linarith

/-- The numerical loss in the singleton-capture union bound is at most one half. -/
theorem sqrt_block_capture_correction (n : ℕ) (v : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hvone : 1 ≤ v)
    (hv : v ≤ (Real.log (n : ℝ)) ^ 2) :
    (v - 1) * (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤
      (1 / 2 : ℝ) := by
  calc
    (v - 1) * (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1))
        ≤ (v - 1) * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_block_pair_ratio n hn) (by linarith)
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) := by ring
    _ ≤ 1 / 2 := log_square_div_sqrt_le_half n hn ht

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- A coarse bound sufficient for absorbing the low Fourier levels. -/
theorem variance_decay_constant {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hlog : t / 3 ≤ Real.log m) :
    4 * m ^ (-(1 : ℝ) / 4) ≤ 1152 / t ^ 2 := by
  have hexp : t ^ 2 / 288 ≤ Real.exp (t / 12) := by
    have h := Real.pow_div_factorial_le_exp (t / 12) (show 0 ≤ t / 12 by positivity) 2
    norm_num at h
    nlinarith
  have hcancel : Real.exp (t / 12) * Real.exp (-(t / 12)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hdecay : t ^ 2 * Real.exp (-(t / 12)) ≤ 288 := by
    have h := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-(t / 12)))
    rw [hcancel] at h
    nlinarith
  have hpow : m ^ (-(1 : ℝ) / 4) ≤ Real.exp (-(t / 12)) := by
    rw [Real.rpow_def_of_pos hm]
    apply Real.exp_le_exp.mpr
    linarith
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  have h := mul_le_mul_of_nonneg_left hpow (sq_nonneg t)
  nlinarith

/-- Cancellation of the bias and comparison of logarithms in the Fourier tail. -/
theorem variance_tail_constant {t m σ : ℝ} (ht : 0 < t)
    (hlog : t / 3 ≤ Real.log m) (hσ : 0 < σ) :
    2 * σ ^ 2 / (σ * Real.log m / 64) ^ 2 ≤ 73728 / t ^ 2 := by
  have hl : 0 < Real.log m := by linarith
  have heq : 2 * σ ^ 2 / (σ * Real.log m / 64) ^ 2 =
      8192 / (Real.log m) ^ 2 := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hl) (sq_pos_of_pos ht)).mpr
  have htl : t ≤ 3 * Real.log m := by linarith
  have hs := mul_le_mul htl htl ht.le (by positivity : 0 ≤ 3 * Real.log m)
  nlinarith

/-- A numerical bound for the sum of low-degree and spectral-tail contributions.
Only the lower bound on `log m` is needed; no floor or exponential monotonicity
arguments enter this estimate. -/
theorem variance_constant_bound {t m σ : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hlog : t / 3 ≤ Real.log m) (hσ : 0 < σ) :
    4 * m ^ (-(1 : ℝ) / 4) + 2 * σ ^ 2 / (σ * Real.log m / 64) ^ 2 ≤
      (2 : ℝ) ^ 17 / t ^ 2 := by
  have h₁ := variance_decay_constant ht hm hlog
  have h₂ := variance_tail_constant ht hlog hσ
  have h₃ : (1152 : ℝ) / t ^ 2 + 73728 / t ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    norm_num
  linarith

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

lemma block_scale_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) :=
  Real.sqrt_pos.mpr (mul_pos hp (sub_pos.mpr hp1))

lemma block_scale_le_half (p : ℝ) :
    Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith [sq_nonneg (p - 1 / 2)]

lemma block_cutoff_pos (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 := by
  have hscale := block_scale_pos hp hp1
  have hlog := log_sqrt_block_lower n hn ht
  have hlogpos : 0 < Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by linarith
  positivity

lemma block_cutoff_le_log_div_128 (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) / 128 := by
  have hsize := sqrt_block_size_bounds n hn ht
  have hmpos : 0 < (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊)
  have hmn : (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hsize.2.1
  have hlogupper := Real.log_le_log hmpos hmn
  have hloglower := log_sqrt_block_lower n hn ht
  have hlognonneg : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_right (block_scale_le_half p) hlognonneg
  linarith

lemma block_cutoff_le_log (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) := by
  have h := block_cutoff_le_log_div_128 n p hn ht
  linarith

/-- A global logarithmic bound which avoids any large-parameter decay calculus. -/
lemma log_sq_le_sixteen_sqrt (x : ℝ) (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlin : Real.log x / 4 ≤ Real.exp (Real.log x / 4) := by
    have h := Real.add_one_le_exp (Real.log x / 4)
    linarith
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log x / 4) hlin 2
  have hexp : (Real.exp (Real.log x / 4)) ^ 2 = Real.sqrt x := by
    rw [pow_two, ← Real.exp_add]
    have harg : Real.log x / 4 + Real.log x / 4 = Real.log x / 2 := by ring
    rw [harg, Real.exp_half, Real.exp_log hxpos]
  rw [hexp] at hsquare
  nlinarith

/-- The support-size correction in the random block capture estimate. -/
lemma block_cutoff_sq_div_sqrt_le_half (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 /
        Real.sqrt (n : ℝ) ≤ 1 / 2 := by
  have hcut := block_cutoff_le_log_div_128 n p hn ht
  have hlog := log_sqrt_block_lower n hn ht
  have hlogpos : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by linarith
  have hk : 0 ≤ Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 := by positivity
  have htsquare := mul_le_mul hcut hcut hk (by linarith : 0 ≤ Real.log (n : ℝ) / 128)
  have hsqrt := log_sq_le_sixteen_sqrt (n : ℝ) (by exact_mod_cast (by omega : 1 ≤ n))
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := by positivity
  apply (div_le_iff₀ hsqrtpos).mpr
  nlinarith

/-- The exact pair-correction form needed by uniform block counting. -/
lemma block_cutoff_sq_pair_ratio_le_half (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hratio := sqrt_block_pair_ratio n hn
  have hmul := mul_le_mul_of_nonneg_left hratio
    (sq_nonneg (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64))
  have hbound := block_cutoff_sq_div_sqrt_le_half n p hn ht
  rw [mul_one_div] at hmul
  exact hmul.trans hbound

lemma block_support_pair_correction_le_half (n v : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ))
    (hv : (v : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2) :
    ((v : ℝ) - 1) *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hsize := sqrt_block_size_bounds n hn ht
  have hm : (3 : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by exact_mod_cast hsize.1
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : 0 ≤ ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1) := by
    apply div_nonneg <;> linarith
  have hv' : (v : ℝ) - 1 ≤ (Real.sqrt (p * (1 - p)) *
      Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 := by linarith
  exact (mul_le_mul_of_nonneg_right hv' hratio).trans
    (block_cutoff_sq_pair_ratio_le_half n p hn ht)

/-- The full numerical coefficient for the actual square-root block parameters. -/
theorem graph_block_preconstant_bound (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hp : 0 < p) (hp1 : p < 1) :
    4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-(1 : ℝ) / 4) +
        2 * (Real.sqrt (p * (1 - p))) ^ 2 /
          (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 ≤
      (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2 := by
  have hsize := sqrt_block_size_bounds n hn ht
  exact variance_constant_bound (by linarith)
    (by exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊))
    (log_sqrt_block_lower n hn ht) (block_scale_pos hp hp1)

/-- The elementary coefficient comparison in the small-logarithm branch. -/
theorem small_log_poincare_coefficient (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : Real.log (n : ℝ) ≤ 16) :
    p * (1 - p) ≤ (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2 := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogpos := Real.log_pos hnreal
  have hvar : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  apply hvar.trans
  apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).mpr
  have hsquare := mul_le_mul ht ht hlogpos.le (by norm_num : (0 : ℝ) ≤ 16)
  norm_num at hsquare ⊢
  nlinarith

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.FiniteParseval

open Finset Matrix

variable {α : Type u} {Ω : Type v} [Fintype α] [Fintype Ω] [DecidableEq α] [DecidableEq Ω]

/-- Fourier coefficient for an arbitrary finite weighted system. -/
def coefficient (w : Ω → ℝ) (χ : α → Ω → ℝ) (f : Ω → ℝ) (a : α) : ℝ :=
  ∑ x, w x * f x * χ a x

/-- A square weighted orthonormal system is complete. No positivity is needed
for this algebraic statement. -/
theorem expansion (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (hcard : Fintype.card α = Fintype.card Ω)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f : Ω → ℝ) (x : Ω) :
    (∑ a, coefficient w χ f a * χ a x) = f x := by
  let A : Matrix α Ω ℝ := fun a x => w x * χ a x
  let B : Matrix Ω α ℝ := fun x a => χ a x
  have hAB : A * B = 1 := by
    ext a b
    change (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0
    exact horth a b
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hAB
  have hAf : A *ᵥ f = fun a => coefficient w χ f a := by
    funext a
    simp only [Matrix.mulVec, dotProduct, A, coefficient]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  calc
    (∑ a, coefficient w χ f a * χ a x) = (B *ᵥ (A *ᵥ f)) x := by
      rw [hAf]
      simp only [Matrix.mulVec, dotProduct, B]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = f x := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]

/-- Parseval's bilinear identity for a finite weighted orthonormal system. -/
theorem parseval_bilinear (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (hcard : Fintype.card α = Fintype.card Ω)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f g : Ω → ℝ) :
    (∑ a, coefficient w χ f a * coefficient w χ g a) = ∑ x, w x * f x * g x := by
  simp only [coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ a, (∑ y, w y * f y * χ a y) * (w x * g x * χ a x)) =
        w x * g x * (∑ a, coefficient w χ f a * χ a x) := by
      simp only [Finset.mul_sum, coefficient]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = w x * f x * g x := by rw [expansion w χ hcard horth]; ring

/-- The usual sum-of-squares Parseval identity. -/
theorem parseval (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (hcard : Fintype.card α = Fintype.card Ω)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f : Ω → ℝ) :
    (∑ a, (coefficient w χ f a)^2) = ∑ x, w x * (f x)^2 := by
  simpa only [pow_two, mul_assoc] using parseval_bilinear w χ hcard horth f f

/-- Synthesis using only a selected finite set of spectral coordinates. -/
def synthesis (χ : α → Ω → ℝ) (c : α → ℝ) (s : Finset α) (x : Ω) : ℝ :=
  ∑ a ∈ s, c a * χ a x

omit [Fintype α] [DecidableEq Ω] in
theorem coefficient_synthesis (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (c : α → ℝ) (s : Finset α) (a : α) :
    coefficient w χ (synthesis χ c s) a = if a ∈ s then c a else 0 := by
  unfold coefficient synthesis
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ b ∈ s, ∑ x, w x * (c b * χ b x) * χ a x) =
        ∑ b ∈ s, c b * (∑ x, w x * χ b x * χ a x) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = if a ∈ s then c a else 0 := by simp_rw [horth]; simp

omit [Fintype α] [DecidableEq α] [DecidableEq Ω] in
theorem inner_synthesis (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (f : Ω → ℝ) (c : α → ℝ) (s : Finset α) :
    (∑ x, w x * f x * synthesis χ c s x) =
      ∑ a ∈ s, c a * coefficient w χ f a := by
  simp only [synthesis, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

omit [Fintype α] [DecidableEq Ω] in
theorem synthesis_sq (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (c : α → ℝ) (s : Finset α) :
    (∑ x, w x * (synthesis χ c s x)^2) = ∑ a ∈ s, (c a)^2 := by
  calc
    (∑ x, w x * (synthesis χ c s x)^2) =
        ∑ x, w x * synthesis χ c s x * synthesis χ c s x := by
      simp only [pow_two, mul_assoc]
    _ = ∑ a ∈ s, c a * coefficient w χ (synthesis χ c s) a :=
      inner_synthesis w χ (synthesis χ c s) c s
    _ = ∑ a ∈ s, (c a)^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [coefficient_synthesis w χ horth, ite_eq_left ha, pow_two]

omit [Fintype α] [DecidableEq Ω] in
/-- The algebraic orthogonal-projection identity used by the low-degree
Hölder estimate. -/
theorem projection_inner_eq_sq (w : Ω → ℝ) (χ : α → Ω → ℝ)
    (horth : ∀ a b, (∑ x, w x * χ a x * χ b x) = if a = b then 1 else 0)
    (f : Ω → ℝ) (s : Finset α) :
    (∑ x, w x * f x * synthesis χ (coefficient w χ f) s x) =
      ∑ x, w x * (synthesis χ (coefficient w χ f) s x)^2 := by
  rw [inner_synthesis, synthesis_sq w χ horth]
  simp only [pow_two]

end Problem313.FiniteParseval

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

def scalarWeight (p : ℝ) (b : Bool) : ℝ :=
  if b = true then p else 1 - p

def weight (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, scalarWeight p (x i)

def chi (p : ℝ) (b : Bool) : ℝ :=
  ((if b = true then (1 : ℝ) else 0) - p) / Real.sqrt (p * (1 - p))

def char (p : ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, chi p (x i)

def coeff (p : ℝ) (g : (ι → Bool) → ℝ) (S : Finset ι) : ℝ := by
  classical
  exact ∑ x, weight p x * g x * char p S x

@[simp] theorem scalarWeight_false (p : ℝ) : scalarWeight p false = 1 - p := rfl
@[simp] theorem scalarWeight_true (p : ℝ) : scalarWeight p true = p := rfl
@[simp] theorem chi_false (p : ℝ) :
    chi p false = -p / Real.sqrt (p * (1 - p)) := by simp [chi]
@[simp] theorem chi_true (p : ℝ) :
    chi p true = (1 - p) / Real.sqrt (p * (1 - p)) := rfl
omit [Fintype ι] in
@[simp] theorem char_empty (p : ℝ) (x : ι → Bool) : char p ∅ x = 1 := by
  simp [char]

theorem scalar_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b c : Bool) :
    scalarWeight p c * (1 + chi p b * chi p c) = if b = c then 1 else 0 := by
  have hpos : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
    Real.sq_sqrt hpos.le
  have hn : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  cases b <;> cases c <;> simp only [scalarWeight, chi, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ite_true, zero_sub]
  all_goals field_simp
  all_goals nlinarith [hs]

theorem character_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x y : ι → Bool) :
    weight p y * (∑ S : Finset ι, char p S x * char p S y) =
      if x = y then 1 else 0 := by
  classical
  have hk : (∑ S : Finset ι, char p S x * char p S y) =
      ∏ i, (1 + chi p (x i) * chi p (y i)) := by
    simpa [char, Finset.prod_mul_distrib] using
      (Finset.prod_one_add (f := fun i : ι => chi p (x i) * chi p (y i))
        Finset.univ).symm
  rw [hk, weight, ← Finset.prod_mul_distrib]
  simp_rw [scalar_kernel hp hp1]
  simp [Fintype.prod_ite_zero, funext_iff]

theorem inversion {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    ∑ S : Finset ι, coeff p g S * char p S x = g x := by
  classical
  simp_rw [coeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ S : Finset ι, weight p y * g y * char p S y * char p S x) =
        ∑ y, g y * (weight p y * ∑ S : Finset ι, char p S x * char p S y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = ∑ y, g y * (if x = y then 1 else 0) := by
      simp_rw [character_kernel hp hp1]
    _ = g x := by simp

theorem parseval [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, coeff p g S ^ 2) = ∑ x, weight p x * (g x) ^ 2 := by
  classical
  calc
    (∑ S : Finset ι, coeff p g S ^ 2) =
        ∑ S : Finset ι, ∑ x, weight p x * g x * (coeff p g S * char p S x) := by
      apply Finset.sum_congr rfl
      intro S hS
      conv_lhs => rw [pow_two, coeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      dsimp [coeff]
      ring
    _ = ∑ x, weight p x * g x * (∑ S : Finset ι, coeff p g S * char p S x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ x, weight p x * (g x) ^ 2 := by
      simp_rw [inversion hp hp1]
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem coeff_zero (p : ℝ) (S : Finset ι) :
    coeff p (fun _ : ι → Bool => 0) S = 0 := by
  classical
  simp [coeff]

theorem coeff_add (p : ℝ) (g h : (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => g x + h x) S = coeff p g S + coeff p h S := by
  classical
  simp [coeff, mul_add, add_mul, Finset.sum_add_distrib]

theorem coeff_sub (p : ℝ) (g h : (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => g x - h x) S = coeff p g S - coeff p h S := by
  classical
  simp [coeff, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem coeff_smul (p c : ℝ) (g : (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => c * g x) S = c * coeff p g S := by
  classical
  simp only [coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem coeff_sum {κ : Type v} (p : ℝ) (s : Finset κ)
    (g : κ → (ι → Bool) → ℝ) (S : Finset ι) :
    coeff p (fun x => ∑ j ∈ s, g j x) S = ∑ j ∈ s, coeff p (g j) S := by
  classical
  simp only [coeff, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem inner_parseval [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g h : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, coeff p g S * coeff p h S) =
      ∑ x, weight p x * g x * h x := by
  classical
  calc
    (∑ S : Finset ι, coeff p g S * coeff p h S) =
        ∑ S : Finset ι, ∑ x, weight p x * g x * (coeff p h S * char p S x) := by
      apply Finset.sum_congr rfl
      intro S hS
      conv_lhs => lhs; unfold coeff
      rw [Finset.sum_mul]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      ring
    _ = ∑ x, weight p x * g x * (∑ S : Finset ι, coeff p h S * char p S x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = ∑ x, weight p x * g x * h x := by
      simp_rw [inversion hp hp1]

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma sqrt_variance_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < Real.sqrt (p * (1 - p)) :=
  Real.sqrt_pos.2 (mul_pos hp (sub_pos.2 hp1))

lemma sqrt_variance_sq {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
  Real.sq_sqrt (mul_nonneg hp (sub_nonneg.2 hp1))

@[simp] lemma scalarWeight_sum (p : ℝ) : ∑ b : Bool, scalarWeight p b = 1 := by
  simp [scalarWeight]

@[simp] lemma chi_mean (p : ℝ) :
    ∑ b : Bool, scalarWeight p b * chi p b = 0 := by
  simp only [Fintype.sum_bool, scalarWeight, chi, ite_true,
    Bool.false_eq_true, ite_false]
  ring

lemma chi_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ b : Bool, scalarWeight p b * (chi p b) ^ 2 = 1 := by
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt (sqrt_variance_pos hp hp1)
  have hsq := sqrt_variance_sq (le_of_lt hp) (le_of_lt hp1)
  simp only [Fintype.sum_bool, scalarWeight, chi, ite_true,
    Bool.false_eq_true, ite_false]
  field_simp
  nlinarith

lemma expectation_product (p : ℝ) (g : ι → Bool → ℝ) :
    (∑ x : ι → Bool, weight p x * ∏ i, g i (x i)) =
      ∏ i, ∑ b : Bool, scalarWeight p b * g i b := by
  classical
  simpa only [weight, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun i b => scalarWeight p b * g i b)).symm

lemma char_eq_univ_prod (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    char p S x = ∏ i, if i ∈ S then chi p (x i) else 1 := by
  classical
  simp [char, Finset.prod_ite_mem]

lemma char_inner_product {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S T : Finset ι) :
    (∑ x : ι → Bool, weight p x * char p S x * char p T x) =
      if S = T then 1 else 0 := by
  classical
  have hfactor :
      (∑ x : ι → Bool, weight p x * char p S x * char p T x) =
        ∏ i, ∑ b : Bool, scalarWeight p b *
          ((if i ∈ S then chi p b else 1) *
           (if i ∈ T then chi p b else 1)) := by
    simpa only [char_eq_univ_prod, Finset.prod_mul_distrib, mul_assoc] using
      expectation_product p (fun i b =>
        (if i ∈ S then chi p b else 1) *
        (if i ∈ T then chi p b else 1))
  rw [hfactor]
  by_cases hST : S = T
  · subst T
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro i hi
    by_cases hiS : i ∈ S
    · simpa only [hiS, ite_true, ← pow_two] using chi_second_moment hp hp1
    · simpa only [hiS, ite_false, mul_one] using scalarWeight_sum p
  · simp only [hST, ite_false]
    obtain ⟨i, hi⟩ := not_forall.mp (Finset.ext_iff.not.mp hST)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hiS : i ∈ S
    · have hiT : i ∉ T := by tauto
      simpa only [hiS, hiT, ite_true, ite_false, mul_one, one_mul] using chi_mean p
    · have hiT : i ∈ T := by tauto
      simpa only [hiS, hiT, ite_true, ite_false, mul_one, one_mul] using chi_mean p

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Separate Fourier supports according to whether the distinguished coordinate occurs. -/
def optionFinsetEquiv : Finset (Option ι) ≃ Finset ι ⊕ Finset ι := by
  classical
  refine
    { toFun := fun S => if none ∈ S then Sum.inr S.eraseNone else Sum.inl S.eraseNone
      invFun := Sum.elim (fun S => S.map Function.Embedding.some) Finset.insertNone
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    by_cases h : none ∈ S
    · simp [h, Finset.insert_eq_of_mem h]
    · simp [h]
  · intro S
    cases S <;> simp

theorem sum_option_finset (F : Finset (Option ι) → ℝ) :
    (∑ S, F S) =
      (∑ S : Finset ι, F (S.map Function.Embedding.some)) +
      ∑ S : Finset ι, F (Finset.insertNone S) := by
  classical
  rw [← optionFinsetEquiv.symm.sum_comp F]
  simp [Fintype.sum_sum_type, optionFinsetEquiv]

omit [Fintype ι] in
@[simp] theorem char_map_some (p : ℝ) (S : Finset ι) (x : Option ι → Bool) :
    char p (S.map Function.Embedding.some) x = char p S (fun i => x (some i)) := by
  classical
  simp [char]

omit [Fintype ι] in
@[simp] theorem char_insertNone (p : ℝ) (S : Finset ι) (x : Option ι → Bool) :
    char p (Finset.insertNone S) x =
      chi p (x none) * char p S (fun i => x (some i)) := by
  classical
  simp [char, Finset.insertNone]

/-- A noise-weighted Fourier polynomial separates into its two first-coordinate pieces. -/
theorem synthesis_option (p ρ : ℝ) (c : Finset (Option ι) → ℝ)
    (x : Option ι → Bool) :
    (∑ S, ρ ^ S.card * c S * char p S x) =
      (∑ S : Finset ι, ρ ^ S.card * c (S.map Function.Embedding.some) *
        char p S (fun i => x (some i))) +
      ρ * chi p (x none) *
        ∑ S : Finset ι, ρ ^ S.card * c (Finset.insertNone S) *
          char p S (fun i => x (some i)) := by
  classical
  rw [sum_option_finset]
  simp only [Finset.card_map, char_map_some, Finset.card_insertNone, char_insertNone,
    pow_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem coefficient_energy_option (c : Finset (Option ι) → ℝ) :
    (∑ S, c S ^ 2) =
      (∑ S : Finset ι, c (S.map Function.Embedding.some) ^ 2) +
        ∑ S : Finset ι, c (Finset.insertNone S) ^ 2 :=
  sum_option_finset _

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

/-- Fourier transformation in the exterior variables of a conditional Fourier
coefficient recovers the full Fourier coefficient on the disjoint support. -/
theorem coeff_restricted_coeff (p : ℝ) (f : (ι ⊕ κ → Bool) → ℝ)
    (A : Finset ι) (D : Finset κ) :
    coeff p (fun y => coeff p (fun x => f (Sum.elim x y)) A) D =
      coeff p f (A.disjSum D) := by
  classical
  let : DecidableEq ι := Classical.decEq _
  let : DecidableEq κ := Classical.decEq _
  let : DecidableEq (ι ⊕ κ) := Classical.decEq _
  unfold coeff
  symm
  calc
    (∑ z, weight p z * f z * char p (A.disjSum D) z) =
        ∑ x : ι → Bool, ∑ y : κ → Bool,
          weight p (Sum.elim x y) * f (Sum.elim x y) *
            char p (A.disjSum D) (Sum.elim x y) := by
      calc
        _ = ∑ xy : (ι → Bool) × (κ → Bool),
            weight p (Sum.elim xy.1 xy.2) * f (Sum.elim xy.1 xy.2) *
              char p (A.disjSum D) (Sum.elim xy.1 xy.2) := by
          apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool)
          intro z
          have hz : Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) = z := by
            funext i
            cases i <;> rfl
          simpa only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, Function.comp_def] using
            congrArg (fun z => weight p z * f z * char p (A.disjSum D) z) hz.symm
        _ = _ := Fintype.sum_prod_type _
    _ = ∑ y, weight p y * (∑ x, weight p x * f (Sum.elim x y) * char p A x) *
        char p D y := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      simp only [weight, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        char, Finset.prod_disjSum]
      ring

/-- A conditional Fourier coefficient expands in the exterior characters,
with full Fourier coefficients and no cutoff on the exterior degree. -/
theorem restricted_coeff_expansion {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (A : Finset ι) (y : κ → Bool) :
    coeff p (fun x => f (Sum.elim x y)) A =
      ∑ D : Finset κ, coeff p f (A.disjSum D) * char p D y := by
  classical
  symm
  simpa only [coeff_restricted_coeff] using
    inversion hp hp1 (fun y => coeff p (fun x => f (Sum.elim x y)) A) y

/-- Averaging the square of a conditional coefficient retains all exterior
Fourier degrees. This is the single-coefficient restriction identity. -/
theorem restricted_coeff_sq_average [DecidableEq κ] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (A : Finset ι) :
    (∑ y : κ → Bool, weight p y *
      (coeff p (fun x => f (Sum.elim x y)) A) ^ 2) =
      ∑ D : Finset κ, (coeff p f (A.disjSum D)) ^ 2 := by
  classical
  symm
  simpa only [coeff_restricted_coeff] using
    parseval hp hp1 (fun y => coeff p (fun x => f (Sum.elim x y)) A)

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.Spectral

variable {Ω : Type u} {S : Type v} [Fintype Ω] [Fintype S] [DecidableEq S]

def coefficient (w : Ω → ℝ) (χ : S → Ω → ℝ) (f : Ω → ℝ) (s : S) : ℝ :=
  ∑ x, w x * f x * χ s x

def synthesis (χ : S → Ω → ℝ) (a : S → ℝ) (x : Ω) : ℝ :=
  ∑ s, a s * χ s x

def multiplier (w : Ω → ℝ) (χ : S → Ω → ℝ) (symbol : S → ℝ)
    (f : Ω → ℝ) : Ω → ℝ :=
  synthesis χ (fun s => symbol s * coefficient w χ f s)

/-- Orthogonality diagonalizes every spectral multiplier. -/
theorem coefficient_synthesis (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (horth : ∀ s t, (∑ x, w x * χ s x * χ t x) = if s = t then 1 else 0)
    (a : S → ℝ) (t : S) :
    coefficient w χ (synthesis χ a) t = a t := by
  classical
  unfold coefficient synthesis
  calc
    (∑ x, w x * (∑ s, a s * χ s x) * χ t x) =
        ∑ x, ∑ s, a s * (w x * χ s x * χ t x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ s, a s * (∑ x, w x * χ s x * χ t x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = a t := by simp [horth]

/-- The Fourier coefficient of a multiplier is multiplied by its symbol. -/
theorem coefficient_multiplier (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (horth : ∀ s t, (∑ x, w x * χ s x * χ t x) = if s = t then 1 else 0)
    (symbol : S → ℝ) (f : Ω → ℝ) (t : S) :
    coefficient w χ (multiplier w χ symbol f) t = symbol t * coefficient w χ f t :=
  coefficient_synthesis w χ horth _ t

omit [DecidableEq S] in
/-- Finite synthesis/analysis duality, without any orthogonality assumption. -/
theorem inner_synthesis (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (a : S → ℝ) (g : Ω → ℝ) :
    (∑ x, w x * synthesis χ a x * g x) =
      ∑ s, a s * coefficient w χ g s := by
  unfold synthesis coefficient
  calc
    (∑ x, w x * (∑ s, a s * χ s x) * g x) =
        ∑ x, ∑ s, a s * (w x * g x * χ s x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ s, a s * (∑ x, w x * g x * χ s x) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]

omit [DecidableEq S] in
/-- Every real spectral multiplier is self-adjoint. -/
theorem multiplier_self_adjoint (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (symbol : S → ℝ) (f g : Ω → ℝ) :
    (∑ x, w x * multiplier w χ symbol f x * g x) =
      ∑ x, w x * f x * multiplier w χ symbol g x := by
  calc
    _ = ∑ s, (symbol s * coefficient w χ f s) * coefficient w χ g s :=
      inner_synthesis w χ _ g
    _ = ∑ s, (symbol s * coefficient w χ g s) * coefficient w χ f s := by
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ x, w x * multiplier w χ symbol g x * f x :=
      (inner_synthesis w χ _ f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Parseval for an explicitly synthesized function. -/
theorem synthesis_energy (w : Ω → ℝ) (χ : S → Ω → ℝ)
    (horth : ∀ s t, (∑ x, w x * χ s x * χ t x) = if s = t then 1 else 0)
    (a : S → ℝ) :
    (∑ x, w x * (synthesis χ a x)^2) = ∑ s, (a s)^2 := by
  calc
    _ = ∑ x, w x * synthesis χ a x * synthesis χ a x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ s, a s * coefficient w χ (synthesis χ a) s :=
      inner_synthesis w χ a _
    _ = ∑ s, (a s)^2 := by
      simp_rw [coefficient_synthesis w χ horth, pow_two]

end Problem313.Spectral

namespace Problem313.BiasedFourier

variable {ι : Type w} [Fintype ι]

open scoped Classical

/-- The biased noise operator, defined by its Fourier multiplier. -/
def noise (p ρ : ℝ) (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ := by
  classical
  exact ∑ S : Finset ι, ρ ^ S.card * coeff p g S * char p S x

theorem noise_self_adjoint (p ρ : ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * noise p ρ f x * g x) =
      ∑ x, weight p x * f x * noise p ρ g x := by
  classical
  have h := Spectral.multiplier_self_adjoint (weight p) (char p) (fun S => ρ ^ S.card) f g
  simpa only [Spectral.multiplier, Spectral.synthesis, Spectral.coefficient, noise, coeff] using h

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- A pointwise fourth-power estimate with the linear term retained for averaging. -/
lemma fourth_power_centered_bound (a z : ℝ) :
    (a + z) ^ 4 ≤ a ^ 4 + 4 * a ^ 3 * z + 8 * a ^ 2 * z ^ 2 + 3 * z ^ 4 := by
  nlinarith only [sq_nonneg (z * (a - z))]

/-- The scalar two-point estimate used to tensorize biased hypercontractivity.
The noise parameter is `sqrt (p * (1-p)) / 4`; after cancellation of the
normalization in the biased character, its two values are `-p / 4` and
`(1-p) / 4`. This formulation also includes the endpoint biases. -/
theorem biased_two_point_fourth_moment (p a b : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (a - p * b / 4) ^ 4 + p * (a + (1 - p) * b / 4) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h1 := fourth_power_centered_bound a (-p * b / 4)
  have h2 := fourth_power_centered_bound a ((1 - p) * b / 4)
  have h3 := mul_le_mul_of_nonneg_left h1 hq
  have h4 := mul_le_mul_of_nonneg_left h2 hp
  have hvar : 0 ≤ p * (1 - p) := mul_nonneg hp hq
  have hvar1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hpq : (1 - p) ^ 3 + p ^ 3 ≤ 1 := by nlinarith
  have hab : 0 ≤ a ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg b)
  have hb4 : 0 ≤ b ^ 4 := by positivity
  have hvarab := mul_le_mul_of_nonneg_right hvar1 hab
  have hfour := mul_le_mul_of_nonneg_left hpq hvar
  have hfourb := mul_le_mul_of_nonneg_right hfour hb4
  have hvarb := mul_le_mul_of_nonneg_right hvar1 hb4
  nlinarith only [h3, h4, hvarab, hfourb, hvarb, hab, hb4]

/-- Mean and variance decomposition for a two-point law, without division. -/
lemma two_point_second_moment (p u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + p * (1 - p) * (v - u) ^ 2 =
      (1 - p) * u ^ 2 + p * v ^ 2 := by
  ring

/-- The scalar noise contraction in raw function values. This is the
`(1 - ρ) * expectation + ρ * identity` form, suitable for tensor products. -/
theorem biased_two_point_noise_fourth (p ρ u v : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 16 * ρ ^ 2 ≤ p * (1 - p)) :
    let μ := (1 - p) * u + p * v
    (1 - p) * (μ + ρ * (u - μ)) ^ 4 + p * (μ + ρ * (v - μ)) ^ 4 ≤
      ((1 - p) * u ^ 2 + p * v ^ 2) ^ 2 := by
  dsimp only
  have h := biased_two_point_fourth_moment p ((1 - p) * u + p * v)
    (4 * ρ * (v - u)) hp hp1
  have hleft : (1 - p) * u + p * v - p * (4 * ρ * (v - u)) / 4 =
      (1 - p) * u + p * v + ρ * (u - ((1 - p) * u + p * v)) := by ring
  have hright : (1 - p) * u + p * v + (1 - p) * (4 * ρ * (v - u)) / 4 =
      (1 - p) * u + p * v + ρ * (v - ((1 - p) * u + p * v)) := by ring
  rw [hleft, hright] at h
  refine h.trans ?_
  have hc := mul_le_mul_of_nonneg_right hρ (sq_nonneg (v - u))
  have hm := two_point_second_moment p u v
  have hbound : ((1 - p) * u + p * v) ^ 2 + (4 * ρ * (v - u)) ^ 2 ≤
      (1 - p) * u ^ 2 + p * v ^ 2 := by nlinarith only [hc, hm]
  exact pow_le_pow_left₀ (by positivity) hbound 2

/-- Finite-sum formulation of the two-point noise contraction. -/
theorem biased_bool_noise_fourth (p ρ : ℝ) (f : Bool → ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 16 * ρ ^ 2 ≤ p * (1 - p)) :
    let w : Bool → ℝ := fun b => if b = true then p else 1 - p
    let μ := ∑ b, w b * f b
    ∑ b, w b * ((1 - ρ) * μ + ρ * f b) ^ 4 ≤
      (∑ b, w b * (f b) ^ 2) ^ 2 := by
  dsimp only
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  have h := biased_two_point_noise_fourth p ρ (f false) (f true) hp hp1 hρ
  dsimp only at h
  convert h using 1 <;> ring

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- Weighted Cauchy--Schwarz in a form useful for finite product measures. -/
theorem weighted_cauchy_schwarz_sq {α : Type u} (s : Finset α)
    (w u v : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x * u x * v x) ^ 2 ≤
      (∑ x ∈ s, w x * (u x) ^ 2) * (∑ x ∈ s, w x * (v x) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    exact le_of_eq (by ring)

/-- The root-free Minkowski step in tensorization of the fourth moment. -/
theorem weighted_fourth_moment_add_sq {α : Type u} (s : Finset α)
    (w A B : α → ℝ) (a b : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : (∑ x ∈ s, w x * (A x) ^ 4) ≤ a ^ 2)
    (hB : (∑ x ∈ s, w x * (B x) ^ 4) ≤ b ^ 2) :
    (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) ≤ (a + b) ^ 2 := by
  have hcs := weighted_cauchy_schwarz_sq s w (fun x => (A x) ^ 2)
    (fun x => (B x) ^ 2) hw
  have hA0 : 0 ≤ ∑ x ∈ s, w x * (A x) ^ 4 :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (by positivity))
  have hB0 : 0 ≤ ∑ x ∈ s, w x * (B x) ^ 4 :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (by positivity))
  have hprod := mul_le_mul hA hB hB0 (sq_nonneg a)
  have hpow : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := fun x => by ring
  simp_rw [hpow] at hcs
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcross : (∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) ≤ a * b := by
    nlinarith [sq_nonneg ((∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) - a * b)]
  have hexpand : (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) =
      (∑ x ∈ s, w x * (A x) ^ 4) +
      2 * (∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) +
      (∑ x ∈ s, w x * (B x) ^ 4) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hexpand]
  nlinarith

/-- A version of the fourth-moment Minkowski step with two nonnegative coefficients. -/
theorem weighted_fourth_moment_combo {α : Type u} (s : Finset α)
    (w A B : α → ℝ) (a b c d : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : (∑ x ∈ s, w x * (A x) ^ 4) ≤ a ^ 2)
    (hB : (∑ x ∈ s, w x * (B x) ^ 4) ≤ b ^ 2) :
    (∑ x ∈ s, w x * (c * (A x) ^ 2 + d * (B x) ^ 2) ^ 2) ≤
      (c * a + d * b) ^ 2 := by
  have hA' : (∑ x ∈ s, w x * (Real.sqrt c * A x) ^ 4) ≤ (c * a) ^ 2 := by
    calc
      _ = c ^ 2 * (∑ x ∈ s, w x * (A x) ^ 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_pow, show Real.sqrt c ^ 4 = c ^ 2 by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hc]]
        ring
      _ ≤ c ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left hA (sq_nonneg c)
      _ = _ := by ring
  have hB' : (∑ x ∈ s, w x * (Real.sqrt d * B x) ^ 4) ≤ (d * b) ^ 2 := by
    calc
      _ = d ^ 2 * (∑ x ∈ s, w x * (B x) ^ 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_pow, show Real.sqrt d ^ 4 = d ^ 2 by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hd]]
        ring
      _ ≤ d ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_left hB (sq_nonneg d)
      _ = _ := by ring
  have h := weighted_fourth_moment_add_sq s w
    (fun x => Real.sqrt c * A x) (fun x => Real.sqrt d * B x)
    (c * a) (d * b) hw (mul_nonneg hc ha) (mul_nonneg hd hb) hA' hB'
  simpa only [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hd] using h

/-- A fourth-moment contraction tensorizes with a two-point contraction.
No linearity assumptions are needed for this analytic step. -/
theorem fourth_moment_tensor_bool {α : Type u} [Fintype α]
    (w : α → ℝ) (q : Bool → ℝ)
    (T : (α → ℝ) → α → ℝ) (S : (Bool → ℝ) → Bool → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hq : ∀ b, 0 ≤ q b)
    (hT : ∀ g, (∑ x, w x * (T g x) ^ 4) ≤ (∑ x, w x * (g x) ^ 2) ^ 2)
    (hS : ∀ g, (∑ b, q b * (S g b) ^ 4) ≤ (∑ b, q b * (g b) ^ 2) ^ 2)
    (g : Bool → α → ℝ) :
    (∑ x, ∑ b, w x * q b * (S (fun c => T (g c) x) b) ^ 4) ≤
      (∑ b, ∑ x, q b * w x * (g b x) ^ 2) ^ 2 := by
  classical
  have ha : 0 ≤ ∑ x, w x * (g false x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have hb : 0 ≤ ∑ x, w x * (g true x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  calc
    _ = ∑ x, w x * (∑ b, q b * (S (fun c => T (g c) x) b) ^ 4) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ x, w x * (∑ b, q b * (T (g b) x) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hS _) (hw x)
    _ = ∑ x, w x * (q false * (T (g false) x) ^ 2 +
        q true * (T (g true) x) ^ 2) ^ 2 := by
      simp only [Fintype.sum_bool, add_comm]
    _ ≤ (q false * (∑ x, w x * (g false x) ^ 2) +
        q true * (∑ x, w x * (g true x) ^ 2)) ^ 2 :=
      weighted_fourth_moment_combo Finset.univ w (T (g false)) (T (g true))
        _ _ (q false) (q true) (fun x _ => hw x) ha hb (hq false) (hq true)
        (hT _) (hT _)
    _ = _ := by
      simp only [Fintype.sum_bool, Finset.mul_sum]
      congr 1
      ring_nf

end Problem313

end

end OAI
end
end

section
section
/-!
Finite biased Fourier analysis and scalar and tensor fourth-moment estimates.
-/
end
end

section
section
namespace OAI


/-! Elementary support-graph combinatorics, independent of probability. -/

namespace Problem313.SupportCombinatorics

open Finset

variable {α : Type u} [DecidableEq α]

/-- The non-isolated vertices of a finite edge family. -/
def vertices (S : Finset (Finset α)) : Finset α := S.biUnion id

/-- The number of support edges incident to a vertex. -/
def degree (S : Finset (Finset α)) (u : α) : ℕ :=
  (S.filter (fun e => u ∈ e)).card

lemma edge_subset_vertices {S : Finset (Finset α)} {e : Finset α}
    (he : e ∈ S) : e ⊆ vertices S := by
  intro u hu
  exact mem_biUnion.mpr ⟨e, he, hu⟩

lemma card_vertices_le {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) : (vertices S).card ≤ 2 * S.card := by
  calc
    (vertices S).card ≤ ∑ e ∈ S, e.card := card_biUnion_le
    _ = 2 * S.card := by
      rw [sum_congr rfl hS]
      simp [Nat.mul_comm]

lemma degree_pos_iff {S : Finset (Finset α)} {u : α} :
    0 < degree S u ↔ u ∈ vertices S := by
  simp [degree, vertices, card_pos, Finset.Nonempty]

lemma degree_le_card_vertices_sub_one {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) (u : α) :
    degree S u ≤ (vertices S).card - 1 := by
  have hinj : Set.InjOn (fun e : Finset α => e.erase u) (S.filter (fun e => u ∈ e)) := by
    intro e he f hf hef
    have he' := (mem_filter.mp he).2
    have hf' := (mem_filter.mp hf).2
    calc
      e = insert u (e.erase u) := (insert_erase he').symm
      _ = insert u (f.erase u) := congrArg (insert u) hef
      _ = f := insert_erase hf'
  have hsub : (S.filter (fun e => u ∈ e)).image (fun e => e.erase u) ⊆
      ((vertices S).erase u).powersetCard 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    obtain ⟨hfS, huf⟩ := mem_filter.mp hf
    apply mem_powersetCard.mpr
    constructor
    · exact erase_subset_erase u (edge_subset_vertices hfS)
    · rw [card_erase_of_mem huf, hS f hfS]
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj, card_powersetCard, Nat.choose_one_right] at hcard
  by_cases hu : u ∈ vertices S
  · simpa [degree, card_erase_of_mem hu] using hcard
  · have hd : degree S u = 0 := by
      have := degree_pos_iff.not.mpr hu
      omega
    simp [hd]

lemma sum_degrees {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) :
    ∑ u ∈ vertices S, degree S u = 2 * S.card := by
  classical
  conv_lhs => simp only [degree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    ∑ e ∈ S, ∑ u ∈ vertices S, (if u ∈ e then (1 : ℕ) else 0) = ∑ e ∈ S, e.card := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      have hh : (vertices S).filter (fun u => u ∈ e) = e := by
        ext u
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun hu => edge_subset_vertices he hu)
      simp [hh]
    _ = 2 * S.card := by
      rw [sum_congr rfl hS]
      simp [Nat.mul_comm]

lemma exists_small_positive_degree {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) (hne : S.Nonempty) :
    ∃ u ∈ vertices S, 1 ≤ degree S u ∧ (degree S u)^2 ≤ 2 * S.card := by
  have hv : (vertices S).Nonempty := by
    obtain ⟨e, he⟩ := hne
    have hepos : 0 < e.card := by rw [hS e he]; omega
    obtain ⟨u, hu⟩ := card_pos.mp hepos
    exact ⟨u, edge_subset_vertices he hu⟩
  obtain ⟨u, hu, hmin⟩ := exists_min_image (vertices S) (degree S) hv
  refine ⟨u, hu, degree_pos_iff.mpr hu, ?_⟩
  have hsum : (vertices S).card * degree S u ≤ 2 * S.card := by
    calc
      (vertices S).card * degree S u = ∑ v ∈ vertices S, degree S u := by simp
      _ ≤ ∑ v ∈ vertices S, degree S v := sum_le_sum (fun v hv => hmin v hv)
      _ = 2 * S.card := sum_degrees hS
  have hdeg := degree_le_card_vertices_sub_one hS u
  have hle : degree S u ≤ (vertices S).card := hdeg.trans (Nat.sub_le _ _)
  calc
    (degree S u)^2 = degree S u * degree S u := pow_two _
    _ ≤ (vertices S).card * degree S u := Nat.mul_le_mul_right _ hle
    _ ≤ 2 * S.card := hsum

end Problem313.SupportCombinatorics

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

open Finset

lemma support_vertices_image {n : ℕ} (S : Finset (GraphEdge n)) :
    SupportCombinatorics.vertices (S.image Subtype.val) = S.biUnion Subtype.val := by
  ext u
  simp [SupportCombinatorics.vertices]

lemma support_degree_image {n : ℕ} (S : Finset (GraphEdge n)) (u : Fin n) :
    SupportCombinatorics.degree (S.image Subtype.val) u =
      (S.filter (fun e => u ∈ e.val)).card := by
  classical
  unfold SupportCombinatorics.degree
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ Subtype.val_injective

lemma graph_support_vertices_card_le {n : ℕ} (S : Finset (GraphEdge n)) :
    (S.biUnion Subtype.val).card ≤ 2 * S.card := by
  classical
  have hS : ∀ e ∈ S.image Subtype.val, e.card = 2 := by
    intro e he
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
    exact e.property
  have h := SupportCombinatorics.card_vertices_le hS
  rw [support_vertices_image, Finset.card_image_of_injective _ Subtype.val_injective] at h
  exact h

lemma exists_graph_support_degree_sq_le {n : ℕ} (S : Finset (GraphEdge n))
    (hne : S.Nonempty) :
    ∃ u ∈ S.biUnion Subtype.val,
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      (S.filter (fun e => u ∈ e.val)).card ^ 2 ≤ 2 * S.card := by
  classical
  have hS : ∀ e ∈ S.image Subtype.val, e.card = 2 := by
    intro e he
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
    exact e.property
  obtain ⟨u, hu, hd, hsq⟩ := SupportCombinatorics.exists_small_positive_degree
    hS (hne.image Subtype.val)
  rw [support_vertices_image] at hu
  rw [support_degree_image] at hd hsq
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hsq
  exact ⟨u, hu, hd, hsq⟩

/-- The graph support vertex needed in block-capture, already in the real cutoff form. -/
lemma exists_graph_support_degree_le {n : ℕ} (S : Finset (GraphEdge n))
    (hne : S.Nonempty) {k : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion Subtype.val,
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k := by
  obtain ⟨u, hu, hd, hsq⟩ := exists_graph_support_degree_sq_le S hne
  refine ⟨u, hu, hd, ?_⟩
  have hsq' : ((S.filter (fun e => u ∈ e.val)).card : ℝ) ^ 2 ≤
      2 * (S.card : ℝ) := by exact_mod_cast hsq
  nlinarith [sq_nonneg (((S.filter (fun e => u ∈ e.val)).card : ℝ) - k)]

lemma graph_support_vertices_card_le_cutoff {n : ℕ} (S : Finset (GraphEdge n))
    {k : ℝ} (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ((S.biUnion Subtype.val).card : ℝ) ≤ k ^ 2 := by
  have h : ((S.biUnion Subtype.val).card : ℝ) ≤ 2 * (S.card : ℝ) := by
    exact_mod_cast graph_support_vertices_card_le S
  linarith

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- If a block meets the vertex support in one vertex, precisely that vertex's
incident support edges survive restriction to the block. -/
theorem block_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => (e.val ∩ B).Nonempty) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, v, hv⟩
    have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
    have hvE : v ∈ e.val := (Finset.mem_inter.mp hv).1
    have hvS : v ∈ S.biUnion (fun e => e.val) :=
      Finset.mem_biUnion.mpr ⟨e, he, hvE⟩
    have hvu : v = u := by
      have : v ∈ ({u} : Finset (Fin n)) := h ▸ Finset.mem_inter.mpr ⟨hvB, hvS⟩
      exact Finset.mem_singleton.mp this
    exact ⟨he, hvu ▸ hvE⟩
  · rintro ⟨he, huE⟩
    have hu : u ∈ B ∩ S.biUnion (fun e => e.val) := by rw [h]; simp
    exact ⟨he, u, Finset.mem_inter.mpr ⟨huE, (Finset.mem_inter.mp hu).1⟩⟩

/-- Cardinal version of deterministic capture by a singleton vertex intersection. -/
theorem block_filter_card_eq_vertex_degree {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    (S.filter (fun e => (e.val ∩ B).Nonempty)).card =
      (S.filter (fun e => u ∈ e.val)).card := by
  rw [block_filter_eq_vertex_filter S B u h]

/-- The singleton-intersection event detects every support with a vertex
of degree between one and the requested cutoff. -/
theorem block_captures_of_singleton_inter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n) (k : ℝ)
    (h : B ∩ S.biUnion (fun e => e.val) = {u})
    (hpos : 1 ≤ (S.filter (fun e => u ∈ e.val)).card)
    (hdeg : ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k) :
    1 ≤ (S.filter (fun e => (e.val ∩ B).Nonempty)).card ∧
      ((S.filter (fun e => (e.val ∩ B).Nonempty)).card : ℝ) ≤ k := by
  rw [block_filter_card_eq_vertex_degree S B u h]
  exact ⟨hpos, hdeg⟩

/-- The same capture identity with the disjointness predicate used for free edges. -/
theorem block_not_disjoint_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => ¬Disjoint e.val B) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  simpa only [Finset.not_disjoint_iff, Finset.Nonempty, Finset.mem_inter] using
    block_filter_eq_vertex_filter S B u h

/-- The free-edge intersection formulation of deterministic block capture. -/
theorem block_inter_free_edges_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  rw [← block_not_disjoint_filter_eq_vertex_filter S B u h]
  ext e
  simp

/-- Counting singleton-intersection blocks gives a lower bound for counting
blocks that capture the support in the desired degree range. -/
theorem count_capturing_blocks_ge_singleton_inter {n : ℕ}
    (S : Finset (GraphEdge n)) (blocks : Finset (Finset (Fin n)))
    (u : Fin n) (k : ℝ)
    (hpos : 1 ≤ (S.filter (fun e => u ∈ e.val)).card)
    (hdeg : ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k) :
    (blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u})).card ≤
      (blocks.filter (fun B =>
        1 ≤ (S.filter (fun e => (e.val ∩ B).Nonempty)).card ∧
        ((S.filter (fun e => (e.val ∩ B).Nonempty)).card : ℝ) ≤ k)).card := by
  classical
  apply Finset.card_le_card
  intro B hB
  obtain ⟨hmem, hsingle⟩ := Finset.mem_filter.mp hB
  exact Finset.mem_filter.mpr
    ⟨hmem, block_captures_of_singleton_inter S B u k hsingle hpos hdeg⟩

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

/-- Probability of an event for a uniformly chosen fixed-size subset. -/
def blockProbability (U : Finset α) (m : ℕ) (P : Finset α → Prop) : ℝ := by
  classical
  exact (((U.powersetCard m).filter P).card : ℝ) / (U.powersetCard m).card

omit [DecidableEq α] in
theorem blockProbability_eq (U : Finset α) (m : ℕ) (P : Finset α → Prop)
    [DecidablePred P] : blockProbability U m P =
      (((U.powersetCard m).filter P).card : ℝ) / (U.powersetCard m).card := by
  unfold blockProbability
  congr

omit [DecidableEq α] in
theorem blockProbability_nonneg (U : Finset α) (m : ℕ) (P : Finset α → Prop) :
    0 ≤ blockProbability U m P := by
  unfold blockProbability
  positivity

omit [DecidableEq α] in
theorem blockProbability_mono (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B → Q B) :
    blockProbability U m P ≤ blockProbability U m Q := by
  classical
  unfold blockProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (U.powersetCard m).filter P ⊆
      (U.powersetCard m).filter Q from by
    intro B hB
    obtain ⟨hB, hP⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨hB, hPQ B hB hP⟩)

theorem blockProbability_mem_count (U : Finset α) {m : ℕ} {u : α}
    (hu : u ∈ U) (hm : 1 ≤ m) :
    ((U.powersetCard m).filter (fun B => u ∈ B)).card =
      (U.card - 1).choose (m - 1) := by
  classical
  simpa using Finset.card_filter_powersetCard_subset {u} U m
    (Finset.singleton_subset_iff.mpr hu) (by simpa using hm)

theorem choose_pred_ratio {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((n - 1).choose (m - 1) : ℝ) / n.choose m = (m : ℝ) / n := by
  have hn : 1 ≤ n := hm.trans hmn
  have hchoose : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hid := Nat.add_one_mul_choose_eq (n - 1) (m - 1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hm] at hid
  have hid' : (n : ℝ) * ((n - 1).choose (m - 1) : ℝ) =
      (n.choose m : ℝ) * m := by exact_mod_cast hid
  apply (div_eq_div_iff hchoose hn0).mpr
  nlinarith

theorem blockProbability_mem (U : Finset α) {m : ℕ} {u : α}
    (hu : u ∈ U) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => u ∈ B) = (m : ℝ) / U.card := by
  classical
  rw [blockProbability_eq, blockProbability_mem_count U hu hm, Finset.card_powersetCard]
  exact choose_pred_ratio hm hmn

theorem blockProbability_pair_count (U : Finset α) {m : ℕ} {u v : α}
    (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v) (hm : 2 ≤ m) :
    ((U.powersetCard m).filter (fun B => u ∈ B ∧ v ∈ B)).card =
      (U.card - 2).choose (m - 2) := by
  simpa [huv, Finset.insert_subset_iff, Finset.singleton_subset_iff] using Finset.card_filter_powersetCard_subset {u, v} U m
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hu, hv⟩) (by simpa [huv] using hm)

theorem choose_two_pred_ratio {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ((n - 2).choose (m - 2) : ℝ) / n.choose m =
      (m : ℝ) / n * ((m : ℝ) - 1) / ((n : ℝ) - 1) := by
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := hm1.trans hmn
  have hmid : ((n - 1).choose (m - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show m - 1 ≤ n - 1 by omega)).ne'
  calc
    ((n - 2).choose (m - 2) : ℝ) / n.choose m =
        (((n - 1 - 1).choose (m - 1 - 1) : ℝ) / (n - 1).choose (m - 1)) *
          (((n - 1).choose (m - 1) : ℝ) / n.choose m) := by
      simp only [Nat.sub_sub]; norm_num only at *
      field_simp
    _ = ((m - 1 : ℕ) : ℝ) / (n - 1 : ℕ) * ((m : ℝ) / n) := by
      rw [choose_pred_ratio (by omega : 1 ≤ m - 1) (by omega : m - 1 ≤ n - 1),
        choose_pred_ratio hm1 hmn]
    _ = _ := by
      rw [Nat.cast_sub hm1, Nat.cast_sub hn1]
      push_cast
      ring

theorem blockProbability_pair (U : Finset α) {m : ℕ} {u v : α}
    (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v) (hm : 2 ≤ m)
    (hmn : m ≤ U.card) :
    blockProbability U m (fun B => u ∈ B ∧ v ∈ B) =
      (m : ℝ) / U.card * ((m : ℝ) - 1) / ((U.card : ℝ) - 1) := by
  classical
  rw [blockProbability_eq, blockProbability_pair_count U hu hv huv hm,
    Finset.card_powersetCard]
  exact choose_two_pred_ratio hm hmn

omit [DecidableEq α] in
theorem blockProbability_congr (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B ↔ Q B) :
    blockProbability U m P = blockProbability U m Q := by
  apply le_antisymm
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mp)
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mpr)

omit [DecidableEq α] in
@[simp] theorem blockProbability_false (U : Finset α) (m : ℕ) :
    blockProbability U m (fun _ => False) = 0 := by
  simp [blockProbability]

theorem blockProbability_or_le (U : Finset α) (m : ℕ)
    (P Q : Finset α → Prop) :
    blockProbability U m (fun B => P B ∨ Q B) ≤
      blockProbability U m P + blockProbability U m Q := by
  classical
  simp only [blockProbability_eq, Finset.filter_or]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le ((U.powersetCard m).filter P)
    ((U.powersetCard m).filter Q)

theorem blockProbability_exists_le (U : Finset α) (m : ℕ)
    (V : Finset α) (P : α → Finset α → Prop) :
    blockProbability U m (fun B => ∃ v ∈ V, P v B) ≤
      ∑ v ∈ V, blockProbability U m (P v) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert v V hv ih =>
      have hcongr : blockProbability U m (fun B => ∃ w ∈ insert v V, P w B) =
          blockProbability U m (fun B => P v B ∨ ∃ w ∈ V, P w B) := by
        apply blockProbability_congr
        intro B hB
        simp
      rw [hcongr, Finset.sum_insert hv]
      exact (blockProbability_or_le U m _ _).trans (add_le_add le_rfl ih)

theorem blockProbability_avoid_ge (U : Finset α) (m : ℕ)
    (V : Finset α) (P : Finset α → Prop) (Q : α → Finset α → Prop) :
    blockProbability U m P - ∑ v ∈ V, blockProbability U m (fun B => P B ∧ Q v B) ≤
      blockProbability U m (fun B => P B ∧ ∀ v ∈ V, ¬ Q v B) := by
  classical
  have hcover : blockProbability U m P ≤
      blockProbability U m (fun B => (P B ∧ ∀ v ∈ V, ¬ Q v B) ∨
        ∃ v ∈ V, P B ∧ Q v B) := by
    apply blockProbability_mono
    intro B hB hP
    by_cases h : ∀ v ∈ V, ¬ Q v B
    · exact Or.inl ⟨hP, h⟩
    · push Not at h
      obtain ⟨v, hv, hQ⟩ := h
      exact Or.inr ⟨v, hv, hP, hQ⟩
  have hbound := hcover.trans ((blockProbability_or_le U m _ _).trans
    (add_le_add le_rfl (blockProbability_exists_le U m V (fun v B => P B ∧ Q v B))))
  linarith

theorem inter_eq_singleton_iff_mem_avoid (B V : Finset α) {u : α} (hu : u ∈ V) :
    B ∩ V = {u} ↔ u ∈ B ∧ ∀ v ∈ V.erase u, v ∉ B := by
  constructor
  · intro h
    constructor
    · have hmem : u ∈ B ∩ V := by rw [h]; simp
      exact (Finset.mem_inter.mp hmem).1
    · intro v hv hvB
      have hvV := (Finset.mem_erase.mp hv).2
      have hmem : v ∈ B ∩ V := Finset.mem_inter.mpr ⟨hvB, hvV⟩
      rw [h, Finset.mem_singleton] at hmem
      exact (Finset.mem_erase.mp hv).1 hmem
  · rintro ⟨huB, havoid⟩
    ext v
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hvB, hvV⟩
      by_contra hvu
      exact havoid v (Finset.mem_erase.mpr ⟨hvu, hvV⟩) hvB
    · rintro rfl
      exact ⟨huB, hu⟩

/-- A union bound conditioned on containing a specified vertex. -/
theorem blockProbability_singleton_inter_ge (U V : Finset α) {m : ℕ} {u : α}
    (hVU : V ⊆ U) (hu : u ∈ V) (hm : 2 ≤ m) (hmn : m ≤ U.card) :
    (m : ℝ) / U.card *
        (1 - ((V.card : ℝ) - 1) * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) ≤
      blockProbability U m (fun B => B ∩ V = {u}) := by
  classical
  have h := blockProbability_avoid_ge U m (V.erase u) (fun B => u ∈ B)
    (fun v B => v ∈ B)
  have hevent : blockProbability U m (fun B => u ∈ B ∧ ∀ v ∈ V.erase u, v ∉ B) =
      blockProbability U m (fun B => B ∩ V = {u}) := by
    apply blockProbability_congr
    intro B hB
    exact (inter_eq_singleton_iff_mem_avoid B V hu).symm
  rw [hevent, blockProbability_mem U (hVU hu) (by omega) hmn] at h
  have hsum : (∑ v ∈ V.erase u, blockProbability U m (fun B => u ∈ B ∧ v ∈ B)) =
      ((V.card : ℝ) - 1) *
        ((m : ℝ) / U.card * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) := by
    calc
      _ = ∑ _v ∈ V.erase u,
          ((m : ℝ) / U.card * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact blockProbability_pair U (hVU hu) (hVU (Finset.mem_erase.mp hv).2)
          (Ne.symm (Finset.mem_erase.mp hv).1) hm hmn
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hu]
        rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨u, hu⟩)]
        norm_num
  rw [hsum] at h
  convert h using 1; ring

/-- At most the sum of the individual inclusion probabilities can touch a fixed set. -/
theorem blockProbability_inter_nonempty_le (U E : Finset α) {m : ℕ}
    (hEU : E ⊆ U) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => (B ∩ E).Nonempty) ≤
      (E.card : ℝ) * m / U.card := by
  classical
  calc
    _ = blockProbability U m (fun B => ∃ v ∈ E, v ∈ B) := by
      apply blockProbability_congr
      intro B hB
      simp only [Finset.Nonempty, Finset.mem_inter]
      aesop
    _ ≤ ∑ v ∈ E, blockProbability U m (fun B => v ∈ B) :=
      blockProbability_exists_le U m E (fun v B => v ∈ B)
    _ = ∑ _v ∈ E, (m : ℝ) / U.card := by
      apply Finset.sum_congr rfl
      intro v hv
      exact blockProbability_mem U (hEU hv) hm hmn
    _ = _ := by simp [nsmul_eq_mul, mul_div_assoc]

/-- The graph-edge touch bound used when averaging the block restriction. -/
theorem blockProbability_edge_touch_le (U E : Finset α) {m : ℕ}
    (hEU : E ⊆ U) (hE : E.card = 2) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => (B ∩ E).Nonempty) ≤ (2 : ℝ) * m / U.card := by
  simpa [hE] using blockProbability_inter_nonempty_le U E hEU hm hmn

/-- Collision estimate reduced to a half yields the usual capture lower bound. -/
theorem blockProbability_singleton_inter_ge_half (U V : Finset α) {m : ℕ} {u : α}
    (hVU : V ⊆ U) (hu : u ∈ V) (hm : 2 ≤ m) (hmn : m ≤ U.card)
    (hcollision : ((V.card : ℝ) - 1) * ((m : ℝ) - 1) / ((U.card : ℝ) - 1) ≤ 1 / 2) :
    (m : ℝ) / (2 * U.card) ≤ blockProbability U m (fun B => B ∩ V = {u}) := by
  have hn : 0 ≤ (m : ℝ) / U.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply le_trans _ (blockProbability_singleton_inter_ge U V hVU hu hm hmn)
  calc
    (m : ℝ) / (2 * U.card) = ((m : ℝ) / U.card) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hn

end Problem313

end

end OAI
end
end

section
section
namespace OAI

namespace Problem313

open Finset

lemma support_vertices_card_le {n : ℕ} (S : Finset (GraphEdge n)) :
    (S.biUnion (fun e => e.val)).card ≤ 2 * S.card := by
  classical
  have h := SupportCombinatorics.card_vertices_le
    (S := S.image Subtype.val) (by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact f.property)
  have hv : SupportCombinatorics.vertices (S.image Subtype.val) =
      S.biUnion (fun e => e.val) := by
    ext u
    simp [SupportCombinatorics.vertices]
  simpa [hv, card_image_of_injective S Subtype.val_injective] using h

lemma support_exists_small_positive_degree {n : ℕ} (S : Finset (GraphEdge n))
    (hS : S.Nonempty) :
    ∃ u ∈ S.biUnion (fun e => e.val),
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      (S.filter (fun e => u ∈ e.val)).card ^ 2 ≤ 2 * S.card := by
  classical
  obtain ⟨u, hu, hpos, hsmall⟩ := SupportCombinatorics.exists_small_positive_degree
    (S := S.image Subtype.val) (by
      intro e he
      obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact f.property) (hS.image Subtype.val)
  have hdeg : SupportCombinatorics.degree (S.image Subtype.val) u =
      (S.filter (fun e => u ∈ e.val)).card := by
    unfold SupportCombinatorics.degree
    rw [filter_image]
    exact card_image_of_injective _ Subtype.val_injective
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa [SupportCombinatorics.vertices] using hu
  · simpa [hdeg] using hpos
  · simpa [hdeg, card_image_of_injective S Subtype.val_injective] using hsmall

lemma support_exists_degree_le_cutoff {n : ℕ} (S : Finset (GraphEdge n))
    (hS : S.Nonempty) {k : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion (fun e => e.val),
      1 ≤ (S.filter (fun e => u ∈ e.val)).card ∧
      ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k := by
  obtain ⟨u, hu, hpos, hsquare⟩ := support_exists_small_positive_degree S hS
  refine ⟨u, hu, hpos, ?_⟩
  have hsquare' : ((S.filter (fun e => u ∈ e.val)).card : ℝ)^2 ≤ 2 * S.card :=
    by exact_mod_cast hsquare
  nlinarith [Nat.cast_nonneg (α := ℝ) (S.filter (fun e => u ∈ e.val)).card]

end Problem313

end OAI
end
end

section
section
namespace OAI


/-!
# Averaging and capture of nonnegative spectral mass

For any finite family of nonnegative masses and random detection events,
if every low-degree support is detected with probability at least `a`, an
upper bound on the average detected mass bounds the low-degree mass.
-/

namespace Problem313

open scoped BigOperators

section FiniteCapture

variable {ι : Type u} {β : Type v} [Fintype ι] [Fintype β]

/-- Interchange averaging over blocks and summing the mass of captured supports. -/
theorem weighted_capture_sum_swap
    (w : β → ℝ) (mass : ι → ℝ) (detect : β → ι → Prop)
    [DecidableRel detect] :
    (∑ b, w b * ∑ i, if detect b i then mass i else 0) =
      ∑ i, (∑ b, if detect b i then w b else 0) * mass i := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

/-- A pointwise detection lower bound controls the mass on any chosen finite set. -/
theorem capture_mass_mul_le
    (low : Finset ι) (mass detection : ι → ℝ) (a : ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (hdet : ∀ i, 0 ≤ detection i)
    (hlow : ∀ i ∈ low, a ≤ detection i) :
    a * ∑ i ∈ low, mass i ≤ ∑ i, detection i * mass i := by
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ low, a * mass i ≤ ∑ i ∈ low, detection i * mass i := by
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hlow i hi) (hmass i)
    _ ≤ ∑ i, detection i * mass i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
        (fun i hi hnot => mul_nonneg (hdet i) (hmass i))

/-- The same capture inequality stated directly with finite block averaging. -/
theorem averaged_capture_mass_mul_le
    (low : Finset ι) (w : β → ℝ) (mass : ι → ℝ)
    (detect : β → ι → Prop) [DecidableRel detect] (a : ℝ)
    (hw : ∀ b, 0 ≤ w b) (hmass : ∀ i, 0 ≤ mass i)
    (hlow : ∀ i ∈ low, a ≤ ∑ b, if detect b i then w b else 0) :
    a * ∑ i ∈ low, mass i ≤
      ∑ b, w b * ∑ i, if detect b i then mass i else 0 := by
  rw [weighted_capture_sum_swap]
  apply capture_mass_mul_le low mass _ a hmass
  · intro i
    apply Finset.sum_nonneg
    intro b hb
    split_ifs
    · exact hw b
    · exact le_rfl
  · exact hlow

/-- Cancel the random-block detection factor. The factor `4` is exactly the
ratio between the edge-touch upper bound `2*m/n` and detection `m/(2*n)`. -/
theorem block_capture_mass_le
    (low : Finset ι) (w : β → ℝ) (mass : ι → ℝ)
    (detect : β → ι → Prop) [DecidableRel detect]
    (m n Q : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hw : ∀ b, 0 ≤ w b) (hmass : ∀ i, 0 ≤ mass i)
    (hlow : ∀ i ∈ low, m / (2 * n) ≤ ∑ b, if detect b i then w b else 0)
    (haverage : (∑ b, w b * ∑ i, if detect b i then mass i else 0) ≤
      (2 * m / n) * Q) :
    (∑ i ∈ low, mass i) ≤ 4 * Q := by
  have ha : 0 < m / (2 * n) := div_pos hm (mul_pos (by norm_num) hn)
  have h := (averaged_capture_mass_mul_le low w mass detect (m / (2 * n))
    hw hmass hlow).trans haverage
  have heq : (2 * m / n) * Q = (m / (2 * n)) * (4 * Q) := by ring
  rw [heq] at h
  exact (mul_le_mul_iff_right₀ ha).mp h

end FiniteCapture

end Problem313

end OAI
end
end

section
section
namespace OAI

/-! The graph-combinatorial input to capture of low Fourier levels. -/

namespace Problem313

noncomputable section

/-- A block detects a support when the restricted Fourier degree is positive
and no larger than the specified real cutoff. -/
def BlockDetects {n : ℕ} (k : ℝ) (S : Finset (GraphEdge n))
    (B : Finset (Fin n)) : Prop :=
  1 ≤ (S.filter (fun e => ¬Disjoint e.val B)).card ∧
    ((S.filter (fun e => ¬Disjoint e.val B)).card : ℝ) ≤ k

instance blockDetects_decidable {n : ℕ} (k : ℝ) (S : Finset (GraphEdge n))
    (B : Finset (Fin n)) : Decidable (BlockDetects k S B) :=
  Classical.propDecidable _

/-- For a low-degree support, choose one positive-degree vertex whose isolation
by the random block guarantees detection. -/
theorem exists_vertex_singleton_implies_detection {n : ℕ}
    (S : Finset (GraphEdge n)) (hS : S.Nonempty) {k : ℝ}
    (hk : 0 ≤ k) (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion (fun e => e.val), ∀ B : Finset (Fin n),
      B ∩ S.biUnion (fun e => e.val) = {u} → BlockDetects k S B := by
  classical
  obtain ⟨u, hu, hpos, hdeg⟩ := support_exists_degree_le_cutoff S hS hk hcard
  refine ⟨u, hu, ?_⟩
  intro B hB
  unfold BlockDetects
  rw [block_not_disjoint_filter_eq_vertex_filter S B u hB]
  exact ⟨hpos, hdeg⟩

/-- Transfer any uniform singleton-intersection bound to a detection bound. -/
theorem block_detection_probability_of_singleton {n : ℕ}
    (blocks : Finset (Finset (Fin n))) (S : Finset (GraphEdge n))
    (hS : S.Nonempty) {k a : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2)
    (hsingle : ∀ u ∈ S.biUnion (fun e => e.val),
      a ≤ ((blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u})).card : ℝ) /
        blocks.card) :
    a ≤ ((blocks.filter (BlockDetects k S)).card : ℝ) / blocks.card := by
  classical
  obtain ⟨u, hu, hdetect⟩ := exists_vertex_singleton_implies_detection S hS hk hcard
  apply (hsingle u hu).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg blocks.card)
  exact_mod_cast Finset.card_le_card (show
    blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u}) ⊆
      blocks.filter (BlockDetects k S) from by
    intro B hB
    obtain ⟨hBmem, hBsingle⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨hBmem, hdetect B hBsingle⟩)

/-- The support-vertex bound turns the random-block union-bound error into a
uniform error at most one half. -/
theorem support_singleton_error_le_half {n : ℕ}
    (S : Finset (GraphEdge n)) (k r : ℝ)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2)
    (hr : 0 ≤ r) (hbudget : k ^ 2 * r ≤ 1 / 2) :
    (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r ≤ 1 / 2 := by
  have hv : ((S.biUnion (fun e => e.val)).card : ℝ) ≤ 2 * S.card := by
    exact_mod_cast support_vertices_card_le S
  have hvk : ((S.biUnion (fun e => e.val)).card : ℝ) - 1 ≤ k ^ 2 := by
    linarith
  exact (mul_le_mul_of_nonneg_right hvk hr).trans hbudget

/-- Quantitative detection from the singleton-intersection union bound. The
scalar `r` will be `(m-1)/(n-1)` for a uniformly chosen `m`-vertex block. -/
theorem block_detection_probability_lower {n : ℕ}
    (blocks : Finset (Finset (Fin n))) (S : Finset (GraphEdge n))
    (hS : S.Nonempty) (k q r : ℝ) (hk : 0 ≤ k) (hq : 0 ≤ q)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) (hr : 0 ≤ r)
    (hbudget : k ^ 2 * r ≤ 1 / 2)
    (hsingle : ∀ u ∈ S.biUnion (fun e => e.val),
      q * (1 - (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r) ≤
        ((blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u})).card : ℝ) /
          blocks.card) :
    q / 2 ≤ ((blocks.filter (BlockDetects k S)).card : ℝ) / blocks.card := by
  apply block_detection_probability_of_singleton blocks S hS hk hcard
  intro u hu
  apply le_trans _ (hsingle u hu)
  have he := support_singleton_error_le_half S k r hcard hr hbudget
  have := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤
    1 - (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r by linarith) hq
  linarith

/-- The biased Fourier cutoff for a square-root block never exceeds `log n`. -/
theorem sqrt_block_cutoff_le_log (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    0 ≤ sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ∧
      sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) := by
  have hm := sqrt_block_size_bounds n hn ht
  have hmreal : (1 : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega)
  have hlogm : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := Real.log_nonneg hmreal
  have hlogmn : Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by linarith)
    exact_mod_cast hm.2.1
  have hprod := mul_le_mul_of_nonneg_right hsigma1 hlogm
  exact ⟨div_nonneg (mul_nonneg hsigma hlogm) (by norm_num), by linarith⟩

/-- Uniform numerical budget used in detecting supports of at most `k²/2` edges. -/
theorem sqrt_block_cutoff_budget (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hk := sqrt_block_cutoff_le_log n sigma hn ht hsigma hsigma1
  have hsq := pow_le_pow_left₀ hk.1 hk.2 2
  calc
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_block_pair_ratio n hn) (sq_nonneg _)
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) := by ring
    _ ≤ 1 / 2 := log_square_div_sqrt_le_half n hn ht

/-- Every nonempty support of degree at most `k²/2` is detected with probability
at least `m/(2*n)` by the square-root-sized random block. -/
theorem sqrt_block_detection_probability (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2)
    (S : Finset (GraphEdge n)) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2) :
    (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 * n) ≤
      blockProbability (Finset.univ : Finset (Fin n)) ⌊Real.sqrt (n : ℝ)⌋₊
        (BlockDetects (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) S) := by
  classical
  let m := ⌊Real.sqrt (n : ℝ)⌋₊
  let k := sigma * Real.log (m : ℝ) / 64
  have hm := sqrt_block_size_bounds n hn ht
  have hk := sqrt_block_cutoff_le_log n sigma hn ht hsigma hsigma1
  obtain ⟨u, hu, hdetect⟩ := exists_vertex_singleton_implies_detection S hS hk.1 hcard
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hr : 0 ≤ ((m : ℝ) - 1) / ((n : ℝ) - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hcollision := support_singleton_error_le_half S k
    (((m : ℝ) - 1) / ((n : ℝ) - 1)) hcard hr
    (sqrt_block_cutoff_budget n sigma hn ht hsigma hsigma1)
  have hsingle := blockProbability_singleton_inter_ge_half
    (Finset.univ : Finset (Fin n)) (S.biUnion (fun e => e.val))
    (Finset.subset_univ _) hu (show 2 ≤ m by omega)
    (show m ≤ (Finset.univ : Finset (Fin n)).card by
      simpa only [Finset.card_univ, Fintype.card_fin] using hm.2.1)
    (by simpa only [Finset.card_univ, Fintype.card_fin, mul_div_assoc] using hcollision)
  have hmono := blockProbability_mono (Finset.univ : Finset (Fin n)) m
    (fun B _ hB => hdetect B hB)
  simpa only [Finset.card_univ, Fintype.card_fin] using hsingle.trans hmono

/-- The graph-bias version, with the normalized cardinal ratio exposed for the
finite averaging lemma. No restriction on `p` is needed for this combinatorics. -/
theorem graph_block_detection_probability (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ))
    (S : Finset (GraphEdge n)) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤
      (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2) :
    (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 * n) ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard ⌊Real.sqrt (n : ℝ)⌋₊).filter
        (BlockDetects (Real.sqrt (p * (1 - p)) *
          Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) S)).card : ℝ) /
        ((Finset.univ : Finset (Fin n)).powersetCard ⌊Real.sqrt (n : ℝ)⌋₊).card := by
  have hsigma1 : Real.sqrt (p * (1 - p)) ≤ (1 / 2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (p - 1 / 2)]
  simpa only [blockProbability_eq] using sqrt_block_detection_probability n
    (Real.sqrt (p * (1 - p))) hn ht (Real.sqrt_nonneg _) hsigma1 S hS hcard

/-- An equivalent presentation using intersection with the finite free-edge set. -/
theorem blockDetects_iff_inter_free_edges {n : ℕ} (k : ℝ)
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) :
    BlockDetects k S B ↔
      1 ≤ (S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B)).card ∧
        ((S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B)).card : ℝ) ≤ k := by
  classical
  have h : S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B) =
      S.filter (fun e => ¬Disjoint e.val B) := by
    ext e
    simp
  rw [h]
  rfl

end

end Problem313

end OAI
end
end

section
section

end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

@[simp] theorem permEdge_refl {n : ℕ} (e : GraphEdge n) :
    permEdge (Equiv.refl _) e = e := by
  apply Subtype.ext
  simp [permEdge]

@[simp] theorem permEdge_permEdge {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (e : GraphEdge n) :
    permEdge π (permEdge ρ e) = permEdge (ρ.trans π) e := by
  apply Subtype.ext
  simp [permEdge, Finset.map_map]

@[simp] theorem permEdge_symm_permEdge {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) : permEdge π.symm (permEdge π e) = e := by
  simp

@[simp] theorem permEdge_permEdge_symm {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) : permEdge π (permEdge π.symm e) = e := by
  simp

def permEdgeEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) : GraphEdge n ≃ GraphEdge n where
  toFun := permEdge π
  invFun := permEdge π.symm
  left_inv := permEdge_symm_permEdge π
  right_inv := permEdge_permEdge_symm π

@[simp] theorem permuteConfig_refl {n : ℕ} (x : GraphConfig n) :
    permuteConfig (Equiv.refl _) x = x := by
  funext e
  simp [permuteConfig]

@[simp] theorem permuteConfig_perm {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (x : GraphConfig n) :
    permuteConfig π (permuteConfig ρ x) = permuteConfig (ρ.trans π) x := by
  funext e
  simp [permuteConfig, permEdge_permEdge]

@[simp] theorem permuteConfig_symm_permuteConfig {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : permuteConfig π.symm (permuteConfig π x) = x := by
  simp

@[simp] theorem permuteConfig_permuteConfig_symm {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : permuteConfig π (permuteConfig π.symm x) = x := by
  simp

def permuteConfigEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) :
    GraphConfig n ≃ GraphConfig n where
  toFun := permuteConfig π
  invFun := permuteConfig π.symm
  left_inv := permuteConfig_symm_permuteConfig π
  right_inv := permuteConfig_permuteConfig_symm π

theorem permEdge_transitive {n : ℕ} (e e' : GraphEdge n) :
    ∃ π : Equiv.Perm (Fin n), permEdge π e = e' := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq e.val e'.val (e.property.trans e'.property.symm)
  exact ⟨π, Subtype.ext hπ⟩

@[simp] theorem graphWeight_permuteConfig {n : ℕ} (p : ℝ)
    (π : Equiv.Perm (Fin n)) (x : GraphConfig n) :
    graphWeight p (permuteConfig π x) = graphWeight p x := by
  classical
  exact (permEdgeEquiv π.symm).prod_comp (fun e => if x e = true then p else 1 - p)

@[simp] theorem permuteConfig_update {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) (e : GraphEdge n) (b : Bool) :
    permuteConfig π (Function.update x e b) =
      Function.update (permuteConfig π x) (permEdge π e) b := by
  classical
  exact Function.update_comp_equiv x (permEdgeEquiv π.symm) e b

theorem edgeInfluence_permEdge {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hf : VertexInvariant f) (π : Equiv.Perm (Fin n)) (e : GraphEdge n) :
    edgeInfluence p f (permEdge π e) = edgeInfluence p f e := by
  classical
  unfold edgeInfluence
  rw [← (permuteConfigEquiv π).sum_comp]
  change (∑ x : GraphConfig n,
    if f (Function.update (permuteConfig π x) (permEdge π e) true) ≠
      f (Function.update (permuteConfig π x) (permEdge π e) false)
    then graphWeight p (permuteConfig π x) else 0) = _
  simp_rw [← permuteConfig_update, hf π, graphWeight_permuteConfig]

theorem edgeInfluence_eq {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hf : VertexInvariant f) (e e' : GraphEdge n) :
    edgeInfluence p f e = edgeInfluence p f e' := by
  obtain ⟨π, rfl⟩ := permEdge_transitive e e'
  exact (edgeInfluence_permEdge p f hf π e).symm

theorem totalInfluence_eq_card_mul {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool)
    (hf : VertexInvariant f) (e : GraphEdge n) :
    totalInfluence p f = Fintype.card (GraphEdge n) * edgeInfluence p f e := by
  classical
  unfold totalInfluence
  simp_rw [edgeInfluence_eq p f hf _ e]
  simp

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313
namespace Reindex

variable {ι : Type u} {κ : Type v}

def config (e : ι ≃ κ) (x : ι → Bool) : κ → Bool := fun j => x (e.symm j)

def configEquiv (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun := config e
  invFun := config e.symm
  left_inv x := by ext i; simp [config]
  right_inv x := by ext i; simp [config]

@[simp] theorem config_apply (e : ι ≃ κ) (x : ι → Bool) (i : ι) :
    config e x (e i) = x i := by simp [config]

@[simp] theorem configEquiv_apply (e : ι ≃ κ) (x : ι → Bool) :
    configEquiv e x = config e x := rfl

theorem config_update [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (x : ι → Bool) (i : ι) (b : Bool) :
    config e (Function.update x i b) = Function.update (config e x) (e i) b := by
  classical
  ext j
  by_cases h : j = e i
  · subst j; simp [config]
  · have h' : e.symm j ≠ i := by
      intro he
      apply h
      simpa using congrArg e he
    simp [config, h, h']

def weight [Fintype ι] (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then p else 1 - p

def influence [Fintype ι] (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x, if f (Function.update x i true) ≠ f (Function.update x i false)
    then weight p x else 0

theorem weight_config [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (p : ℝ) (x : ι → Bool) : weight p (config e x) = weight p x := by
  unfold weight
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

theorem influence_config [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (p : ℝ) (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool)
    (hfg : ∀ x, g (config e x) = f x) (i : ι) :
    influence p g (e i) = influence p f i := by
  classical
  unfold influence
  apply Eq.symm
  apply Fintype.sum_equiv (configEquiv e)
  intro x
  simp only [configEquiv_apply, ← config_update, hfg, weight_config]

theorem weight_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) : 0 ≤ weight p x := by
  unfold weight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith

theorem influence_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) : 0 ≤ influence p f i := by
  classical
  unfold influence
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact weight_nonneg hp0 hp1 x
  · exact le_rfl

/-- An orbit of at least `m` equally influential coordinates bounds each influence. -/
theorem influence_le_total_div [Fintype ι] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → Bool) (i : ι)
    (S : Finset ι) {m : ℝ} (hm : 0 < m) (hcard : m ≤ (S.card : ℝ))
    (heq : ∀ j ∈ S, influence p f j = influence p f i) :
    influence p f i ≤ (∑ j, influence p f j) / m := by
  classical
  have hi := influence_nonneg hp0 hp1 f i
  have hS : (S.card : ℝ) * influence p f i = ∑ j ∈ S, influence p f j := by
    calc
      (S.card : ℝ) * influence p f i = ∑ _j ∈ S, influence p f i := by simp
      _ = ∑ j ∈ S, influence p f j := Finset.sum_congr rfl (fun j hj => (heq j hj).symm)
  have hsum : (∑ j ∈ S, influence p f j) ≤ ∑ j, influence p f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j hj hjS
    exact influence_nonneg hp0 hp1 f j
  apply (le_div_iff₀ hm).2
  calc
    influence p f i * m = m * influence p f i := mul_comm _ _
    _ ≤ (S.card : ℝ) * influence p f i := mul_le_mul_of_nonneg_right hcard hi
    _ = ∑ j ∈ S, influence p f j := hS
    _ ≤ ∑ j, influence p f j := hsum

end Reindex
end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

/-- An edge is free in a block restriction when it touches the block. -/
def EdgeTouches {n : ℕ} (B : Finset (Fin n)) (e : GraphEdge n) : Prop :=
  ∃ v, v ∈ e.val ∧ v ∈ B

/-- The vertex permutation is supported on the block. -/
def SupportedOnBlock {n : ℕ} (B : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ v, v ∉ B → π v = v

lemma supportedOnBlock_mem_iff {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) (v : Fin n) :
    π v ∈ B ↔ v ∈ B := by
  constructor
  · intro h
    by_contra hn
    exact hn (by simpa [hπ v hn] using h)
  · intro h
    by_contra hn
    have he := hπ (π v) hn
    have he' : π v = v := π.injective he
    exact hn (he'.symm ▸ h)

lemma supportedOnBlock_symm {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) :
    SupportedOnBlock B π.symm := by
  intro v hv
  apply π.injective
  simpa using (hπ v hv).symm

lemma block_mem_permEdge_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) (v : Fin n) :
    v ∈ (permEdge π e).val ↔ π.symm v ∈ e.val := by
  simp [permEdge]

lemma edgeTouches_permEdge_iff {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) (e : GraphEdge n) :
    EdgeTouches B (permEdge π e) ↔ EdgeTouches B e := by
  constructor
  · rintro ⟨v, hv, hB⟩
    refine ⟨π.symm v, (block_mem_permEdge_iff π e v).mp hv, ?_⟩
    exact (supportedOnBlock_mem_iff (supportedOnBlock_symm hπ) v).mpr hB
  · rintro ⟨v, hv, hB⟩
    refine ⟨π v, ?_, (supportedOnBlock_mem_iff hπ v).mpr hB⟩
    simpa [block_mem_permEdge_iff] using hv

lemma permEdge_eq_self_of_not_touches {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (e : GraphEdge n) (he : ¬ EdgeTouches B e) : permEdge π e = e := by
  apply Subtype.ext
  ext v
  rw [block_mem_permEdge_iff]
  constructor
  · intro hv
    have hn : π.symm v ∉ B := fun h => he ⟨π.symm v, hv, h⟩
    have hf := hπ (π.symm v) hn
    have hf' : v = π.symm v := by simpa using hf
    exact hf'.symm ▸ hv
  · intro hv
    have hn : v ∉ B := fun h => he ⟨v, hv, h⟩
    have hf := supportedOnBlock_symm hπ v hn
    simpa [hf] using hv

lemma edgeTouches_iff_not_disjoint {n : ℕ} (B : Finset (Fin n))
    (e : GraphEdge n) : EdgeTouches B e ↔ ¬ Disjoint e.val B := by
  classical
  simp [EdgeTouches, Finset.disjoint_left]

lemma supportedOnBlock_one {n : ℕ} (B : Finset (Fin n)) :
    SupportedOnBlock B (1 : Equiv.Perm (Fin n)) := by
  intro v _
  rfl

lemma supportedOnBlock_mul {n : ℕ} {B : Finset (Fin n)}
    {π σ : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (hσ : SupportedOnBlock B σ) : SupportedOnBlock B (π * σ) := by
  intro v hv
  change π (σ v) = v
  rw [hσ v hv, hπ v hv]

/-- The subgroup of permutations supported on a given vertex block. -/
def blockPermutationSubgroup {n : ℕ} (B : Finset (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π | SupportedOnBlock B π}
  one_mem' := supportedOnBlock_one B
  mul_mem' := supportedOnBlock_mul
  inv_mem' := supportedOnBlock_symm

@[simp] lemma mem_blockPermutationSubgroup {n : ℕ} (B : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : π ∈ blockPermutationSubgroup B ↔ SupportedOnBlock B π :=
  Iff.rfl

lemma supportedOnBlock_swap {n : ℕ} {B : Finset (Fin n)} {u v : Fin n}
    (hu : u ∈ B) (hv : v ∈ B) : SupportedOnBlock B (Equiv.swap u v) := by
  intro w hw
  have hwu : w ≠ u := fun h => hw (h ▸ hu)
  have hwv : w ≠ v := fun h => hw (h ▸ hv)
  simp [Equiv.swap_apply_def, hwu, hwv]

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- Assemble a configuration on a coordinate subset and its complement. -/
def pasteCube {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) : α → β :=
  fun i => if hi : P i then x ⟨i, hi⟩ else y ⟨i, hi⟩

@[simp]
theorem pasteCube_of_pos {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) (i : α) (hi : P i) :
    pasteCube P x y i = x ⟨i, hi⟩ := by
  simp [pasteCube, hi]

@[simp]
theorem pasteCube_of_neg {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) (i : α) (hi : ¬ P i) :
    pasteCube P x y i = y ⟨i, hi⟩ := by
  simp [pasteCube, hi]

/-- A permutation preserving the free coordinates and fixing all exterior coordinates
commutes with pasting, without changing the fixed exterior configuration. -/
theorem pasteCube_reindex {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i)
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) :
    (fun i => pasteCube P x y (π.symm i)) =
      pasteCube P (fun i => x ((π.subtypeEquiv hP).symm i)) y := by
  funext i
  by_cases hi : P i
  · have hi' : P (π.symm i) := (hP _).mpr (by simpa using hi)
    simp only [pasteCube, dite_eq_left hi, dite_eq_left hi']
    rfl
  · have hsi : π.symm i = i := (π.symm_apply_eq).mpr (hfix i hi).symm
    simp [pasteCube, hi, hsi]

/-- Restriction of a function to a coordinate subset, with exterior values fixed. -/
def restrictCube {α : Type u} {β : Type v} {γ : Type w} (P : α → Prop) [DecidablePred P]
    (f : (α → β) → γ) (y : {i // ¬ P i} → β) : ({i // P i} → β) → γ :=
  fun x => f (pasteCube P x y)

/-- Coordinate symmetry survives conditioning outside a set when the symmetry
fixes every exterior coordinate individually. -/
theorem restrictCube_invariant {α : Type u} {β : Type v} {γ : Type w} (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i) (f : (α → β) → γ)
    (hf : ∀ z, f (fun i => z (π.symm i)) = f z)
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) :
    restrictCube P f y (fun i => x ((π.subtypeEquiv hP).symm i)) =
      restrictCube P f y x := by
  unfold restrictCube
  rw [← pasteCube_reindex P π hP hfix x y]
  exact hf _

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- A permutation supported on a finite block can map any two equally sized
subsets of the block to one another. -/
theorem exists_block_perm_map {α : Type u} [Fintype α] [DecidableEq α]
    (B s t : Finset α) (hs : s ⊆ B) (ht : t ⊆ B)
    (hc : s.card = t.card) :
    ∃ π : Equiv.Perm α, (∀ u, u ∉ B → π u = u) ∧
      s.map π.toEmbedding = t := by
  classical
  let sB := s.subtype (· ∈ B)
  let tB := t.subtype (· ∈ B)
  have hsmap : sB.map (Function.Embedding.subtype _) = s :=
    Finset.subtype_map_of_mem hs
  have htmap : tB.map (Function.Embedding.subtype _) = t :=
    Finset.subtype_map_of_mem ht
  have hcB : sB.card = tB.card := by
    have hsc := congrArg Finset.card hsmap
    have htc := congrArg Finset.card htmap
    simpa using hsc.trans (hc.trans htc.symm)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq sB tB hcB
  let π : Equiv.Perm α := σ.extendDomain (Equiv.refl {u // u ∈ B})
  refine ⟨π, ?_, ?_⟩
  · intro u hu
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hu
  · calc
      s.map π.toEmbedding = (sB.map (Function.Embedding.subtype _)).map π.toEmbedding := by
        rw [hsmap]
      _ = (sB.map σ.toEmbedding).map (Function.Embedding.subtype _) := by
        rw [Finset.map_map, Finset.map_map]
        congr 1
        ext u
        exact Equiv.Perm.extendDomain_apply_image σ (Equiv.refl _) u
      _ = t := by rw [hσ, htmap]

/-- The edge orbit under permutations fixing the complement of `B` pointwise. -/
def blockEdgeOrbit {n : ℕ} (B : Finset (Fin n)) (e : GraphEdge n) :
    Finset (GraphEdge n) := by
  classical
  exact Finset.univ.filter (fun e' => ∃ π : Equiv.Perm (Fin n),
    (∀ u, u ∉ B → π u = u) ∧ permEdge π e = e')

@[simp] theorem mem_blockEdgeOrbit {n : ℕ} {B : Finset (Fin n)}
    {e e' : GraphEdge n} : e' ∈ blockEdgeOrbit B e ↔
    ∃ π : Equiv.Perm (Fin n), (∀ u, u ∉ B → π u = u) ∧ permEdge π e = e' := by
  classical
  simp [blockEdgeOrbit]

/-- All edges wholly contained in a block are in one supported-permutation orbit. -/
theorem block_internal_mem_orbit {n : ℕ} {B : Finset (Fin n)}
    {e e' : GraphEdge n} (he : e.val ⊆ B) (he' : e'.val ⊆ B) :
    e' ∈ blockEdgeOrbit B e := by
  obtain ⟨π, hπ, hmap⟩ := exists_block_perm_map B e.val e'.val he he' (e.property.trans e'.property.symm)
  exact mem_blockEdgeOrbit.mpr ⟨π, hπ, Subtype.ext hmap⟩

/-- The number of graph edges wholly contained in a vertex block. -/
theorem card_block_internal_edges {n : ℕ} (B : Finset (Fin n)) :
    (Finset.univ.filter (fun e : GraphEdge n => e.val ⊆ B)).card = B.card.choose 2 := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp he).2, e.property⟩
  · intro e he e' he' h
    exact Subtype.ext h
  · intro s hs
    obtain ⟨hsB, hsc⟩ := Finset.mem_powersetCard.mp hs
    exact ⟨⟨s, hsc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsB⟩, rfl⟩

theorem block_card_le_choose_two (m : ℕ) (hm : 3 ≤ m) : m ≤ m.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  exact Nat.mul_le_mul_left m (by omega)

/-- Internal edge orbits have at least as many edges as the block has vertices. -/
theorem block_internal_orbit_card {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} (hB : 3 ≤ B.card) (he : e.val ⊆ B) :
    B.card ≤ (blockEdgeOrbit B e).card := by
  classical
  calc
    B.card ≤ B.card.choose 2 := block_card_le_choose_two _ hB
    _ = (Finset.univ.filter (fun e' : GraphEdge n => e'.val ⊆ B)).card :=
      (card_block_internal_edges B).symm
    _ ≤ (blockEdgeOrbit B e).card := Finset.card_le_card (by
      intro e' he'
      exact block_internal_mem_orbit he (Finset.mem_filter.mp he').2)

/-- The boundary edge joining a vertex of the block to a fixed exterior vertex. -/
def blockBoundaryEdge {n : ℕ} {B : Finset (Fin n)} (w : Fin n) (hw : w ∉ B)
    (u : B) : GraphEdge n :=
  ⟨{u.val, w}, Finset.card_pair (by
    intro h
    exact hw (h ▸ u.property))⟩

theorem blockBoundaryEdge_injective {n : ℕ} {B : Finset (Fin n)}
    (w : Fin n) (hw : w ∉ B) : Function.Injective (blockBoundaryEdge w hw) := by
  intro u v h
  have he : ({u.val, w} : Finset (Fin n)) = {v.val, w} := congrArg Subtype.val h
  have hu : u.val ∈ ({v.val, w} : Finset (Fin n)) := by rw [← he]; simp
  rcases (show u.val = v.val ∨ u.val = w by simpa using hu) with huv | huw
  · exact Subtype.ext huv
  · exact False.elim (hw (huw ▸ u.property))

/-- Boundary edges with the same exterior endpoint are in one block orbit. -/
theorem block_boundary_mem_orbit {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} {u w : Fin n} (hu : u ∈ B) (hw : w ∉ B)
    (he : e.val = {u, w}) (v : B) :
    blockBoundaryEdge w hw v ∈ blockEdgeOrbit B e := by
  classical
  refine mem_blockEdgeOrbit.mpr ⟨Equiv.swap u v.val, ?_, ?_⟩
  · intro z hz
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hzu
      exact hz (hzu ▸ hu)
    · intro hzv
      exact hz (hzv ▸ v.property)
  · apply Subtype.ext
    have hwu : w ≠ u := by intro h; exact hw (h ▸ hu)
    have hwv : w ≠ v.val := by intro h; exact hw (h ▸ v.property)
    simp [permEdge, blockBoundaryEdge, he, Equiv.swap_apply_of_ne_of_ne hwu hwv]

/-- Boundary edge orbits contain at least one edge for every block vertex. -/
theorem block_boundary_orbit_card {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} {u w : Fin n} (hu : u ∈ B) (hw : w ∉ B)
    (he : e.val = {u, w}) : B.card ≤ (blockEdgeOrbit B e).card := by
  classical
  let emb : B ↪ GraphEdge n := ⟨blockBoundaryEdge w hw, blockBoundaryEdge_injective w hw⟩
  calc
    B.card = (Finset.univ.map emb).card := by simp
    _ ≤ (blockEdgeOrbit B e).card := Finset.card_le_card (by
      intro e' he'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp he'
      exact block_boundary_mem_orbit hu hw he v)

/-- Every edge incident with a block of at least three vertices has a
supported-permutation orbit of cardinality at least the block cardinality. -/
theorem blockEdgeOrbit_card_lower {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} (hB : 3 ≤ B.card) (hmeet : (e.val ∩ B).Nonempty) :
    B.card ≤ (blockEdgeOrbit B e).card := by
  classical
  by_cases he : e.val ⊆ B
  · exact block_internal_orbit_card hB he
  obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp e.property
  by_cases ha : a ∈ B
  · have hb : b ∉ B := by
      intro hb
      apply he
      intro z hz
      rw [heab] at hz
      rcases (show z = a ∨ z = b by simpa using hz) with rfl | rfl
      · exact ha
      · exact hb
    exact block_boundary_orbit_card ha hb heab
  · have hb : b ∈ B := by
      obtain ⟨z, hz⟩ := hmeet
      obtain ⟨hze, hzB⟩ := Finset.mem_inter.mp hz
      rw [heab] at hze
      rcases (show z = a ∨ z = b by simpa using hze) with rfl | rfl
      · exact False.elim (ha hzB)
      · exact hzB
    apply block_boundary_orbit_card hb ha
    simpa [Finset.pair_comm] using heab

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

/-- The supported permutation orbit of a free edge consists only of free edges. -/
theorem blockEdgeOrbit_touches {n : ℕ} {B : Finset (Fin n)}
    {e d : GraphEdge n} (he : EdgeTouches B e) (hd : d ∈ blockEdgeOrbit B e) :
    EdgeTouches B d := by
  obtain ⟨π, hπ, rfl⟩ := mem_blockEdgeOrbit.mp hd
  exact (edgeTouches_permEdge_iff hπ e).mpr he

/-- A free edge has at least `B.card` free-edge orbit mates, with explicit
supported-permutation witnesses. This is the finite-coordinate interface for
conditional influence bounds. -/
theorem exists_freeEdge_orbit_family {n : ℕ} (B : Finset (Fin n))
    (hB : 3 ≤ B.card) (e : {e : GraphEdge n // EdgeTouches B e}) :
    ∃ S : Finset {d : GraphEdge n // EdgeTouches B d},
      B.card ≤ S.card ∧ ∀ d ∈ S, ∃ π : Equiv.Perm (Fin n),
        SupportedOnBlock B π ∧ permEdge π e.val = d.val := by
  classical
  let S := (blockEdgeOrbit B e.val).subtype (EdgeTouches B)
  have hmap : S.map (Function.Embedding.subtype _) = blockEdgeOrbit B e.val :=
    Finset.subtype_map_of_mem (fun d hd => blockEdgeOrbit_touches e.property hd)
  have hcard : S.card = (blockEdgeOrbit B e.val).card := by
    simpa using congrArg Finset.card hmap
  refine ⟨S, ?_, ?_⟩
  · rw [hcard]
    apply blockEdgeOrbit_card_lower hB
    obtain ⟨v, hve, hvB⟩ := e.property
    exact ⟨v, Finset.mem_inter.mpr ⟨hve, hvB⟩⟩
  · intro d hd
    exact mem_blockEdgeOrbit.mp (Finset.mem_subtype.mp hd)

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- Pivotal influences of a conditioned function are invariant under every
coordinate permutation that preserves the free set and fixes its complement. -/
theorem restrictCube_influence_reindex {α : Type u} [Fintype α]
    (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i) (f : (α → Bool) → Bool)
    (hf : ∀ z, f (fun i => z (π.symm i)) = f z)
    (p : ℝ) (y : {i // ¬ P i} → Bool) (i : {i // P i}) :
    Reindex.influence p (restrictCube P f y) ((π.subtypeEquiv hP) i) =
      Reindex.influence p (restrictCube P f y) i := by
  apply Reindex.influence_config (π.subtypeEquiv hP)
  intro x
  exact restrictCube_invariant P π hP hfix f hf x y

/-- Conditional edge influences respect vertex permutations supported on the block. -/
theorem restrictCube_influence_permEdge {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (π : Equiv.Perm (Fin n)) (hπ : SupportedOnBlock B π)
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p : ℝ) (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y)
        ⟨permEdge π e.val, (edgeTouches_permEdge_iff hπ e.val).mpr e.property⟩ =
      Reindex.influence p (restrictCube (EdgeTouches B) f y) e := by
  let hP : ∀ i, EdgeTouches B i ↔ EdgeTouches B ((permEdgeEquiv π) i) :=
    fun i => (edgeTouches_permEdge_iff hπ i).symm
  exact restrictCube_influence_reindex (EdgeTouches B) (permEdgeEquiv π) hP
    (fun i hi => permEdge_eq_self_of_not_touches hπ i hi) f (hf π) p y e

/-- Quantitative conditional influence bound from a finite collection of edges in
one block orbit.  The collection may be supplied on the original edge type. -/
theorem restrictCube_influence_le_of_orbit {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) (S : Finset (GraphEdge n))
    {m : ℝ} (hm : 0 < m) (hcard : m ≤ (S.card : ℝ))
    (horbit : ∀ d ∈ S, ∃ π : Equiv.Perm (Fin n),
      SupportedOnBlock B π ∧ permEdge π e.val = d) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y) e ≤
      (∑ d, Reindex.influence p (restrictCube (EdgeTouches B) f y) d) / m := by
  classical
  have htouch : ∀ d ∈ S, EdgeTouches B d := by
    intro d hd
    obtain ⟨π, hπ, hmap⟩ := horbit d hd
    rw [← hmap]
    exact (edgeTouches_permEdge_iff hπ e.val).mpr e.property
  have hcard' : m ≤ ((S.subtype (EdgeTouches B)).card : ℝ) := by
    simpa only [Finset.card_subtype, Finset.filter_true_of_mem htouch] using hcard
  apply Reindex.influence_le_total_div hp0 hp1 _ e
    (S.subtype (EdgeTouches B)) hm hcard'
  intro d hd
  obtain ⟨π, hπ, hmap⟩ := horbit d.val (Finset.mem_subtype.mp hd)
  simpa only [hmap] using restrictCube_influence_permEdge B π hπ f hf p y e

/-- Every conditional influence on edges touching a block is at most the total
conditional influence divided by the number of block vertices. -/
theorem block_restricted_influence_le {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (hB : 3 ≤ B.card)
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y) e ≤
      (∑ d, Reindex.influence p (restrictCube (EdgeTouches B) f y) d) /
        (B.card : ℝ) := by
  classical
  obtain ⟨S, hcard, horbit⟩ := exists_freeEdge_orbit_family B hB e
  have hm : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
  apply Reindex.influence_le_total_div hp0 hp1 _ e S hm (by exact_mod_cast hcard)
  intro d hd
  obtain ⟨π, hπ, hmap⟩ := horbit d hd
  simpa only [hmap] using restrictCube_influence_permEdge B π hπ f hf p y e

end Problem313

end

end OAI
end
end

section
section
/-! Canonical graph symmetry, supported-edge orbits, support-degree bounds,
and fixed-size vertex-block counting used by the variance proof. -/
end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

@[simp] theorem boolReal_nonneg (b : Bool) : 0 ≤ boolReal b := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by
  cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sq (b : Bool) : boolReal b ^ 2 = boolReal b := by
  cases b <;> norm_num [boolReal]

theorem graphWeight_sum {n : ℕ} (p : ℝ) :
    (∑ x : GraphConfig n, graphWeight p x) = 1 := by
  classical
  unfold graphWeight
  rw [← Fintype.prod_sum (fun (_ : GraphEdge n) (b : Bool) => if b = true then p else 1 - p)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  simp

theorem graphWeight_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : GraphConfig n) : 0 ≤ graphWeight p x := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

theorem graphWeight_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x : GraphConfig n) : 0 < graphWeight p x := by
  classical
  apply Finset.prod_pos
  intro e he
  split_ifs <;> linarith

theorem graphMean_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ graphMean p f := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (graphWeight_nonneg hp hp1 x) (boolReal_nonneg (f x))

theorem graphMean_le_one {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : graphMean p f ≤ 1 := by
  classical
  calc
    graphMean p f ≤ ∑ x : GraphConfig n, graphWeight p x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_of_le_one_right (graphWeight_nonneg hp hp1 x) (boolReal_le_one (f x))
    _ = 1 := graphWeight_sum p

theorem graphMean_mem_Icc {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : graphMean p f ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨graphMean_nonneg hp hp1 f, graphMean_le_one hp hp1 f⟩

theorem graphVariance_eq_mean_mul {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphVariance p f = graphMean p f * (1 - graphMean p f) := by
  classical
  let m := graphMean p f
  change (∑ x : GraphConfig n, graphWeight p x * (boolReal (f x) - m) ^ 2) = m * (1 - m)
  calc
    (∑ x : GraphConfig n, graphWeight p x * (boolReal (f x) - m) ^ 2) =
        ∑ x : GraphConfig n,
          ((1 - 2 * m) * (graphWeight p x * boolReal (f x)) + m ^ 2 * graphWeight p x) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [sub_sq, mul_add, mul_sub, boolReal_sq]
      ring
    _ = (1 - 2 * m) * m + m ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, graphWeight_sum, mul_one]
      rfl
    _ = m * (1 - m) := by ring

@[simp] theorem boolReal_not (b : Bool) : boolReal (!b) = 1 - boolReal b := by
  cases b <;> norm_num [boolReal]

theorem graphMean_not {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphMean p (fun x => !(f x)) = 1 - graphMean p f := by
  classical
  simp only [graphMean, boolReal_not, mul_sub, mul_one, Finset.sum_sub_distrib,
    graphWeight_sum]

theorem graphMean_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : ∃ x, f x = true) : 0 < graphMean p f := by
  classical
  obtain ⟨x, hx⟩ := hf
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (graphWeight_nonneg hp.le hp1.le y) (boolReal_nonneg (f y))
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simpa [hx, boolReal] using graphWeight_pos hp hp1 x

theorem graphMean_lt_one {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : ∃ x, f x = false) : graphMean p f < 1 := by
  obtain ⟨x, hx⟩ := hf
  have ht : ∃ x, (!(f x)) = true := ⟨x, by simp [hx]⟩
  have h := graphMean_pos hp hp1 ht
  rw [graphMean_not] at h
  linarith

theorem graphMean_mem_Ioo {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : NontrivialGraphProperty f) :
    graphMean p f ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨graphMean_pos hp hp1 hf.1, graphMean_lt_one hp hp1 hf.2⟩

theorem graphVariance_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ graphVariance p f := by
  rw [graphVariance_eq_mean_mul]
  exact mul_nonneg (graphMean_nonneg hp hp1 f) (sub_nonneg.mpr (graphMean_le_one hp hp1 f))

theorem graphVariance_le_quarter {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphVariance p f ≤ 1 / 4 := by
  rw [graphVariance_eq_mean_mul]
  nlinarith [sq_nonneg (graphMean p f - 1 / 2)]

theorem edgeInfluence_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) (e : GraphEdge n) : 0 ≤ edgeInfluence p f e := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact graphWeight_nonneg hp hp1 x
  · exact le_rfl

theorem totalInfluence_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ totalInfluence p f := by
  classical
  apply Finset.sum_nonneg
  intro e he
  exact edgeInfluence_nonneg hp hp1 f e

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

@[simp] theorem coeff_empty (p : ℝ) (g : (ι → Bool) → ℝ) :
    coeff p g ∅ = ∑ x, weight p x * g x := by
  classical
  simp [coeff]

/-- Algebraic expansion of finite weighted variance. Positivity is not needed. -/
theorem weighted_variance_eq_second_moment {α : Type v} [Fintype α]
    (w g : α → ℝ) (hw : ∑ x, w x = 1) :
    (∑ x, w x * (g x - ∑ y, w y * g y) ^ 2) =
      (∑ x, w x * g x ^ 2) - (∑ x, w x * g x) ^ 2 := by
  classical
  let μ := ∑ x, w x * g x
  change (∑ x, w x * (g x - μ) ^ 2) = (∑ x, w x * g x ^ 2) - μ ^ 2
  calc
    (∑ x, w x * (g x - μ) ^ 2) =
        ∑ x, (w x * g x ^ 2 - 2 * μ * (w x * g x) + μ ^ 2 * w x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x, w x * g x ^ 2) - 2 * μ * (∑ x, w x * g x) +
        μ ^ 2 * (∑ x, w x) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (∑ x, w x * g x ^ 2) - μ ^ 2 := by
      rw [hw]
      change (∑ x, w x * g x ^ 2) - 2 * μ * μ + μ ^ 2 * 1 = _
      ring

/-- The total mass of the finite Bernoulli product is one, algebraically for every bias. -/
theorem weight_mass_one (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [scalarWeight]

/-- Parseval implies that the variance is exactly the nonconstant spectral mass. -/
theorem variance_eq_nonempty_of_parseval (p : ℝ) (g : (ι → Bool) → ℝ)
    (hparseval : (∑ x, weight p x * g x ^ 2) = ∑ S : Finset ι, coeff p g S ^ 2) :
    (∑ x, weight p x * (g x - coeff p g ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, coeff p g S ^ 2 := by
  rw [coeff_empty, weighted_variance_eq_second_moment _ _ (weight_mass_one p), hparseval]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅), coeff_empty]

/-- The same identity with a nonempty filter, convenient for degree cutoffs. -/
theorem variance_eq_nonempty_filter_of_parseval (p : ℝ) (g : (ι → Bool) → ℝ)
    (hparseval : (∑ x, weight p x * g x ^ 2) = ∑ S : Finset ι, coeff p g S ^ 2) :
    (∑ x, weight p x * (g x - coeff p g ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ≠ ∅), coeff p g S ^ 2 := by
  rw [Finset.filter_ne']
  exact variance_eq_nonempty_of_parseval p g hparseval

theorem variance_eq_nonempty {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (g x - coeff p g ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, coeff p g S ^ 2 := by
  exact variance_eq_nonempty_of_parseval p g (parseval hp hp1 g).symm

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x := by
  apply Finset.prod_nonneg
  intro i hi
  unfold scalarWeight
  split_ifs <;> linarith

/-- A Boolean function has total Fourier mass at most one. -/
theorem boolean_spectral_mass_le_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, coeff p (fun x => boolReal (f x)) S ^ 2) ≤ 1 := by
  rw [parseval hp hp1]
  calc
    (∑ x, weight p x * boolReal (f x) ^ 2) ≤ ∑ x : ι → Bool, weight p x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [boolReal_sq]
      exact mul_le_of_le_one_right (weight_nonneg hp.le hp1.le x) (boolReal_le_one (f x))
    _ = 1 := weight_mass_one p

end Problem313.BiasedFourier

namespace Problem313

open BiasedFourier

@[simp] theorem fourier_weight_eq_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    BiasedFourier.weight p x = graphWeight p x := rfl

@[simp] theorem fourier_coeff_empty_eq_graphMean {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) :
    coeff p (fun x => boolReal (f x)) ∅ = graphMean p f := by
  rw [coeff_empty]
  unfold graphMean
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  rw [fourier_weight_eq_graphWeight]

theorem graph_second_moment_eq_mean {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    (∑ x, BiasedFourier.weight p x * boolReal (f x) ^ 2) = graphMean p f := by
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fourier_weight_eq_graphWeight]
  congr 1
  cases f x <;> norm_num [boolReal]

/-- The graph variance bridge needs only Parseval on the real-valued Boolean encoding. -/
theorem graphVariance_eq_fourier_nonempty_of_parseval {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool)
    (hparseval : (∑ x, BiasedFourier.weight p x * boolReal (f x) ^ 2) =
      ∑ S : Finset (GraphEdge n), coeff p (fun x => boolReal (f x)) S ^ 2) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).erase ∅,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅), ← hparseval,
    graph_second_moment_eq_mean, fourier_coeff_empty_eq_graphMean,
    graphVariance_eq_mean_mul]
  ring

theorem graphVariance_eq_fourier_nonempty {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).erase ∅,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  exact graphVariance_eq_fourier_nonempty_of_parseval p f
    (parseval hp hp1 (fun x : GraphConfig n => boolReal (f x))).symm

theorem graphVariance_eq_fourier_nonempty_filter {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).filter (fun S => S ≠ ∅),
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  rw [Finset.filter_ne']
  exact graphVariance_eq_fourier_nonempty hp hp1 f

theorem graph_fourier_mass_eq_mean {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    (∑ S : Finset (GraphEdge n), coeff p (fun x => boolReal (f x)) S ^ 2) =
      graphMean p f := by
  rw [parseval hp hp1]
  exact graph_second_moment_eq_mean p f

/-- The variance identity as a sum over nonempty Fourier supports. -/
theorem graphVariance_eq_fourier_sum_nonempty {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  simpa only [Finset.nonempty_iff_ne_empty] using
    graphVariance_eq_fourier_nonempty_filter hp hp1 f

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace Problem313

variable {ι : Type u} [DecidableEq ι]

/-- Reinsert one Boolean coordinate in a function on the remaining coordinates. -/
def russoInsert (i : ι) (b : Bool) (z : {j : ι // j ≠ i} → Bool) : ι → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, z)

@[simp] theorem russoInsert_self (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) : russoInsert i b z i = b := by
  simp [russoInsert, Equiv.funSplitAt_symm_apply]

@[simp] theorem russoInsert_of_ne (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) (j : ι) (h : j ≠ i) :
    russoInsert i b z j = z ⟨j,h⟩ := by
  simp [russoInsert, Equiv.funSplitAt_symm_apply, h]

@[simp] theorem update_russoInsert (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    Function.update (russoInsert i b z) i c = russoInsert i c z := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

variable [Fintype ι]

/-- Splitting a finite Boolean cube at one coordinate. -/
theorem sum_bool_split (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x, g x) = ∑ z : {j : ι // j ≠ i} → Bool,
      (g (russoInsert i true z) + g (russoInsert i false z)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp g]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

/-- The product excluding a coordinate does not depend on that coordinate. -/
theorem prod_erase_russoInsert (p : ℝ) (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j ∈ Finset.univ.erase i, if russoInsert i b z j = true then p else 1-p) =
    ∏ j ∈ Finset.univ.erase i, if russoInsert i c z j = true then p else 1-p := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji]

/-- A Bernoulli weight factors at a chosen coordinate. -/
theorem prod_russoInsert (p : ℝ) (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j, if russoInsert i b z j = true then p else 1-p) =
    (if b = true then p else 1-p) *
      ∏ j ∈ Finset.univ.erase i, if russoInsert i false z j = true then p else 1-p := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if russoInsert i b z j = true then p else 1-p) (Finset.mem_univ i)]
  rw [prod_erase_russoInsert p i b false]
  simp

/-- Finite reindexing identity behind the Russo--Margulis derivative formula.
No positivity assumptions on the bias or the observable are needed. -/
theorem russo_sum_reindex (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (if x i = true then (1 : ℝ) else -1) *
      (∏ j ∈ Finset.univ.erase i, if x j = true then p else 1-p) * g x) =
    ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      (g (Function.update x i true) - g (Function.update x i false)) := by
  rw [sum_bool_split i, sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [russoInsert_self, Bool.false_eq_true,
    ↓reduceIte, update_russoInsert, prod_russoInsert]
  rw [prod_erase_russoInsert p i true false]
  ring

/-- Integrating out one coordinate is unchanged by Bernoulli resampling. -/
theorem sum_weight_conditioning (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) * g x) =
    ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      ((1-p) * g (Function.update x i false) + p * g (Function.update x i true)) := by
  rw [sum_bool_split i, sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [update_russoInsert, prod_russoInsert, Bool.false_eq_true, ↓reduceIte]
  ring

/-- A reset observable can be integrated on the cube with that coordinate removed. -/
theorem sum_weight_update (p : ℝ) (i : ι) (b : Bool) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      g (Function.update x i b)) =
    ∑ z : {j : ι // j ≠ i} → Bool,
      (∏ j ∈ Finset.univ.erase i, if russoInsert i false z j = true then p else 1-p) *
      g (russoInsert i b z) := by
  rw [sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [update_russoInsert, prod_russoInsert, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Discrete integration by parts for a centered Bernoulli coordinate. -/
theorem sum_weight_centered_coordinate (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) * g x *
      ((if x i = true then (1 : ℝ) else 0) - p)) =
    p * (1-p) * ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      (g (Function.update x i true) - g (Function.update x i false)) := by
  rw [sum_bool_split i, sum_bool_split i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [russoInsert_self, update_russoInsert, prod_russoInsert,
    Bool.false_eq_true, ↓reduceIte]
  ring

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace Problem313.BiasedFourier

variable {ι : Type u} [DecidableEq ι]

/-- The discrete derivative, retained as a function on the full cube. -/
def delta (i : ι) (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  g (Function.update x i true) - g (Function.update x i false)

@[simp] theorem delta_update (i : ι) (g : (ι → Bool) → ℝ)
    (x : ι → Bool) (b : Bool) :
    delta i g (Function.update x i b) = delta i g x := by
  simp [delta, Function.update_idem]

@[simp] theorem delta_delta_fun (i : ι) (g : (ι → Bool) → ℝ) :
    delta i (delta i g) = 0 := by
  funext x
  simp [delta, Function.update_idem]

@[simp] theorem delta_delta (i : ι) (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    delta i (delta i g) x = 0 := by simp [delta]

private theorem char_update_aux (p : ℝ) (S : Finset ι) (i : ι) (hi : i ∉ S)
    (x : ι → Bool) (b : Bool) : char p S (Function.update x i b) = char p S x := by
  unfold char
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

theorem char_update_of_not_mem (p : ℝ) (S : Finset ι) (x : ι → Bool)
    (i : ι) (b : Bool) (hi : i ∉ S) :
    char p S (Function.update x i b) = char p S x :=
  char_update_aux p S i hi x b

variable [Fintype ι]

/-- Integration by parts against one normalized biased character. -/
theorem integral_chi_eq_sqrt_mul_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * chi p (x i)) =
      Real.sqrt (p * (1-p)) * ∑ x, weight p x * delta i g x := by
  have hpos : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsq : Real.sqrt (p * (1-p)) ^ 2 = p * (1-p) := Real.sq_sqrt hpos.le
  calc
    _ = (∑ x, weight p x * g x * ((if x i = true then (1:ℝ) else 0)-p)) /
          Real.sqrt (p * (1-p)) := by
      simp only [chi, Finset.sum_div, mul_div_assoc]
    _ = (p * (1-p) * ∑ x, weight p x * delta i g x) /
          Real.sqrt (p * (1-p)) := by
      congr 1
      exact sum_weight_centered_coordinate p i g
    _ = _ := by
      apply (div_eq_iff hs).2
      calc
        _ = Real.sqrt (p * (1-p)) ^ 2 * (∑ x, weight p x * delta i g x) := by rw [hsq]
        _ = _ := by ring

/-- Fourier coefficients of a coordinate derivative, with the same full cube on both sides. -/
theorem coeff_insert_eq_sqrt_mul_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (A : Finset ι) (hi : i ∉ A) :
    coeff p g (insert i A) =
      Real.sqrt (p * (1-p)) * coeff p (delta i g) A := by
  classical
  have hpos : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1-p)) ^ 2 = p * (1-p) := Real.sq_sqrt hpos.le
  have hn : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hc := Problem313.sum_weight_centered_coordinate p i (fun x => g x * char p A x)
  have hcenter :
      (∑ x, weight p x * (g x * char p A x) *
        ((if x i = true then (1 : ℝ) else 0)-p)) =
      p * (1-p) * coeff p (delta i g) A := by
    calc
      _ = p * (1-p) * ∑ x, weight p x *
          (g (Function.update x i true) * char p A (Function.update x i true) -
           g (Function.update x i false) * char p A (Function.update x i false)) := hc
      _ = _ := by
        congr 1
        unfold coeff
        apply Finset.sum_congr (by ext; simp)
        intro x hx
        rw [char_update_aux p A i hi, char_update_aux p A i hi]
        unfold delta
        ring
  apply mul_left_cancel₀ hn
  calc
    Real.sqrt (p * (1-p)) * coeff p g (insert i A) =
        ∑ x, weight p x * (g x * char p A x) *
          ((if x i = true then (1 : ℝ) else 0)-p) := by
      rw [coeff, Finset.mul_sum]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      rw [char, Finset.prod_insert hi]
      change Real.sqrt (p * (1-p)) *
        (weight p x * g x * (chi p (x i) * char p A x)) = _
      unfold chi
      field_simp
    _ = p * (1-p) * coeff p (delta i g) A := hcenter
    _ = Real.sqrt (p * (1-p)) *
        (Real.sqrt (p * (1-p)) * coeff p (delta i g) A) := by rw [← mul_assoc, ← pow_two, hs]

/-- Erasing a coordinate from a nonzero-degree coefficient gives the derivative coefficient. -/
theorem coeff_eq_sqrt_mul_delta_erase {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p g S = Real.sqrt (p * (1-p)) * coeff p (delta i g) (S.erase i) := by
  conv_lhs => rw [← Finset.insert_erase hi]
  exact coeff_insert_eq_sqrt_mul_delta hp hp1 g i (S.erase i) (Finset.notMem_erase i S)

/-- Squared Fourier derivative identity, in the normalization used by Dirichlet energy. -/
theorem coeff_sq_eq_variance_mul_delta_erase_sq {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p g S ^ 2 = p * (1-p) * coeff p (delta i g) (S.erase i) ^ 2 := by
  rw [coeff_eq_sqrt_mul_delta_erase hp hp1 g i S hi, mul_pow,
    Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le))]

/-- A coordinate derivative has no Fourier support containing that coordinate. -/
theorem coeff_delta_eq_zero_of_mem {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p (delta i g) S = 0 := by
  classical
  rw [← Finset.insert_erase hi]
  rw [coeff_insert_eq_sqrt_mul_delta hp hp1 (delta i g) i (S.erase i)
    (Finset.notMem_erase i S)]
  simp [coeff]

/-- The Fourier derivative identity with coordinate-first parameter order. -/
theorem coeff_insert_eq_sqrt_mul_coeff_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (i : ι) (g : (ι → Bool) → ℝ) (A : Finset ι) (hi : i ∉ A) :
    coeff p g (insert i A) = Real.sqrt (p * (1-p)) * coeff p (delta i g) A :=
  coeff_insert_eq_sqrt_mul_delta hp hp1 g i A hi

/-- The Fourier derivative identity with coordinate-first parameter order. -/
theorem coeff_delta_eq_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (i : ι) (g : (ι → Bool) → ℝ) (S : Finset ι) (hi : i ∈ S) :
    coeff p (delta i g) S = 0 :=
  coeff_delta_eq_zero_of_mem hp hp1 g i S hi

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
namespace Problem313

@[simp] theorem boolReal_sub_abs (a b : Bool) :
    |boolReal a - boolReal b| = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sub_sq (a b : Bool) :
    (boolReal a - boolReal b) ^ 2 = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sub_fourth (a b : Bool) :
    (boolReal a - boolReal b) ^ 4 = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

theorem boolReal_sub_mem (a b : Bool) :
    boolReal a - boolReal b = -1 ∨ boolReal a - boolReal b = 0 ∨
      boolReal a - boolReal b = 1 := by
  cases a <;> cases b <;> norm_num [boolReal]

theorem boolReal_sub_abs_le_one (a b : Bool) : |boolReal a - boolReal b| ≤ 1 := by
  rw [boolReal_sub_abs]
  split_ifs <;> norm_num

namespace Reindex
variable {ι : Type u} [Fintype ι] [dι : DecidableEq ι]

theorem boolean_delta_abs_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * |boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))|) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_abs, mul_ite, mul_one, mul_zero, influence]

theorem boolean_delta_sq_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * (boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))) ^ 2) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_sq, mul_ite, mul_one, mul_zero, influence]

theorem boolean_delta_fourth_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * (boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))) ^ 4) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_fourth, mul_ite, mul_one, mul_zero, influence]

end Reindex
end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
namespace Problem313
open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Delete a distinguished coordinate to reindex all supports containing it. -/
theorem sum_supports_containing (i : ι) (a : Finset ι → ℝ) :
    (∑ S : Finset ι, if i ∈ S then a S else 0) =
      ∑ S : Finset ι, if i ∉ S then a (insert i S) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun S _ => S.erase i) (fun S _ => insert i S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp
  · intro S hS
    simp
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro S hS
    exact Finset.erase_insert (Finset.mem_filter.mp hS).2
  · intro S hS
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2]

/-- Algebraic coordinate energy identity from the derivative Fourier identities. -/
theorem spectral_coordinate_energy (i : ι) (a b : Finset ι → ℝ) (σ : ℝ)
    (hzero : ∀ S, i ∈ S → b S = 0)
    (hinsert : ∀ S, i ∉ S → a (insert i S) = σ * b S) :
    (∑ S : Finset ι, if i ∈ S then (a S)^2 else 0) =
      σ^2 * ∑ S : Finset ι, (b S)^2 := by
  rw [sum_supports_containing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hi : i ∈ S
  · simp [hi, hzero S hi]
  · simp [hi, hinsert S hi, mul_pow]

/-- Counting each spectral support once for every coordinate it contains. -/
theorem sum_card_mul_eq_sum_mem (a : Finset ι → ℝ) :
    (∑ S : Finset ι, (S.card : ℝ) * a S) =
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S then a S else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp [Finset.sum_ite_mem, nsmul_eq_mul]

/-- Summing coordinate energies gives the finite Dirichlet identity. -/
theorem spectral_dirichlet (a : Finset ι → ℝ) (I : ι → ℝ) (σ : ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι, if i ∈ S then (a S)^2 else 0) = σ^2 * I i) :
    (∑ S : Finset ι, (S.card : ℝ) * (a S)^2) = σ^2 * ∑ i, I i := by
  rw [sum_card_mul_eq_sum_mem]
  simp_rw [hcoord]
  rw [Finset.mul_sum]

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.BiasedFourier

open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The coordinate Dirichlet identity, with only the two derivative coefficient
identities isolated as hypotheses. -/
theorem coordinate_energy_of_coeff_derivative {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g dg : (ι → Bool) → ℝ) (i : ι)
    (hzero : ∀ S, i ∈ S → coeff p dg S = 0)
    (hinsert : ∀ S, i ∉ S → coeff p g (insert i S) =
      Real.sqrt (p * (1 - p)) * coeff p dg S) :
    (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * ∑ x, weight p x * (dg x)^2 := by
  rw [Problem313.spectral_coordinate_energy i (coeff p g) (coeff p dg)
    (Real.sqrt (p * (1 - p))) hzero hinsert]
  rw [parseval hp hp1, Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le))]

/-- Summing coordinate Dirichlet identities gives degree-weighted Fourier energy. -/
theorem total_energy_of_coordinate_energy {p : ℝ}
    (g : (ι → Bool) → ℝ) (E : ι → ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * E i) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p g S)^2) =
      p * (1 - p) * ∑ i, E i := by
  rw [Problem313.sum_card_mul_eq_sum_mem]
  simp_rw [hcoord]
  rw [Finset.mul_sum]

/-- The Fourier mass on supports containing a fixed coordinate equals its
weighted squared discrete derivative. -/
theorem coordinate_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) :
    (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * ∑ x, weight p x * (delta i g x)^2 := by
  exact coordinate_energy_of_coeff_derivative hp hp1 g (delta i g) i
    (fun S hS => coeff_delta_eq_zero_of_mem hp hp1 g i S hS)
    (fun S hS => coeff_insert_eq_sqrt_mul_delta hp hp1 g i S hS)

/-- The full finite-cube Fourier Dirichlet identity for real observables. -/
theorem dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p g S)^2) =
      p * (1 - p) * ∑ i, ∑ x, weight p x * (delta i g x)^2 := by
  exact total_energy_of_coordinate_energy g _ (coordinate_dirichlet hp hp1 g)

/-- For Boolean observables, squared derivative energy is pivotal influence. -/
theorem boolean_coordinate_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    (∑ S : Finset ι, if i ∈ S then (coeff p (fun x => boolReal (f x)) S)^2 else 0) =
      p * (1 - p) * Reindex.influence p f i := by
  rw [coordinate_dirichlet hp hp1]
  congr 1
  simpa only [delta, weight, scalarWeight, Reindex.weight] using
    Reindex.boolean_delta_sq_moment p f i

/-- The degree-weighted Fourier mass of a Boolean function is its total pivotal
influence times the Bernoulli variance. -/
theorem boolean_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * ∑ i, Reindex.influence p f i := by
  exact total_energy_of_coordinate_energy _ _ (boolean_coordinate_dirichlet hp hp1 f)

end Problem313.BiasedFourier

namespace Problem313

/-- The graph Dirichlet identity for pivotal total influence. -/
theorem graph_fourier_dirichlet {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : GraphConfig n → Bool) :
    (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
      (BiasedFourier.coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * totalInfluence p f := by
  classical
  have hi : (∑ e : GraphEdge n, Reindex.influence p f e) = totalInfluence p f := by
    unfold totalInfluence
    apply Finset.sum_congr rfl
    intro e he
    unfold Reindex.influence edgeInfluence
    apply Finset.sum_congr (by ext; simp)
    intro x hx
    congr 1
    congr 4 <;> exact Subsingleton.elim _ _
  have h := BiasedFourier.boolean_dirichlet hp hp1 f
  rw [hi] at h
  exact h

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- A finite spectral tail is controlled by its first degree moment. -/
theorem finite_spectral_tail {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s with cutoff < degree i, mass i) ≤
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  classical
  apply (le_div_iff₀ hcutoff).2
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ s with cutoff < degree i, mass i * cutoff ≤
        ∑ i ∈ s with cutoff < degree i, degree i * mass i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hiq⟩ := Finset.mem_filter.mp hi
      nlinarith [hmass i his]
    _ ≤ ∑ i ∈ s, degree i * mass i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi _
      exact mul_nonneg (hdegree i hi) (hmass i hi)

/-- Splitting at a positive spectral cutoff gives a low-degree term and a tail. -/
theorem finite_spectral_split {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s, mass i) ≤
      (∑ i ∈ s with degree i ≤ cutoff, mass i) +
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => degree i ≤ cutoff) mass
  simp only [not_le] at hsplit
  rw [← hsplit]
  exact add_le_add le_rfl (finite_spectral_tail s mass degree cutoff hcutoff hmass hdegree)

/-- The bias cancels exactly in the tail term at the bias-dependent cutoff. -/
theorem variance_tail_bias_cancellation (sigma ell : ℝ)
    (hsigma : sigma ≠ 0) (hell : ell ≠ 0) :
    sigma ^ 2 / ((sigma * ell / 64) ^ 2 / 2) = 8192 / ell ^ 2 := by
  field_simp
  ring

/-- Assemble low-degree capture and the Dirichlet identity into a variance bound. -/
theorem variance_from_spectral_capture {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i)
    (hcapture : (∑ i ∈ s with degree i ≤ (sigma * ell / 64) ^ 2 / 2, mass i)
      ≤ lowConstant * influence)
    (hdirichlet : (∑ i ∈ s, degree i * mass i) = sigma ^ 2 * influence) :
    (∑ i ∈ s, mass i) ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  have hcutoff : 0 < (sigma * ell / 64) ^ 2 / 2 := by positivity
  have hsplit := finite_spectral_split s mass degree _ hcutoff hmass hdegree
  have htail : sigma ^ 2 * influence / ((sigma * ell / 64) ^ 2 / 2) =
      (8192 / ell ^ 2) * influence := by
    calc
      _ = (sigma ^ 2 / ((sigma * ell / 64) ^ 2 / 2)) * influence := by ring
      _ = _ := by rw [variance_tail_bias_cancellation sigma ell hsigma.ne' hell.ne']
  rw [hdirichlet, htail] at hsplit
  nlinarith

/-- The two numerical terms fit inside the advertised universal constant. -/
theorem variance_constant_assembly (t ell lowConstant : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell)
    (hlow : lowConstant ≤ 256 / t ^ 2) :
    lowConstant + 8192 / ell ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by positivity : 0 < t / 3) hell
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t / 3) hell
  have htail : 8192 / ell ^ 2 ≤ 73728 / t ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hellpos) (sq_pos_of_pos ht)).2
    nlinarith
  have hbudget : 256 / t ^ 2 + 73728 / t ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · norm_num
    · positivity
  linarith

/-- A more flexible numerical budget, useful with coarse exponential estimates. -/
theorem variance_constant_assembly_budget (t ell lowConstant budget : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell)
    (hlow : lowConstant ≤ budget / t ^ 2)
    (hbudget : budget + 73728 ≤ (2 : ℝ) ^ 17) :
    lowConstant + 8192 / ell ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by positivity : 0 < t / 3) hell
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t / 3) hell
  have htail : 8192 / ell ^ 2 ≤ 73728 / t ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hellpos) (sq_pos_of_pos ht)).2
    nlinarith
  calc
    lowConstant + 8192 / ell ^ 2 ≤ budget / t ^ 2 + 73728 / t ^ 2 :=
      add_le_add hlow htail
    _ = (budget + 73728) / t ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbudget (sq_nonneg t)

/-- A small logarithm only needs the elementary Poincaré bound. -/
theorem variance_small_log_assembly (t variance influence : ℝ)
    (ht : 0 < t) (htsmall : t ≤ 16) (hinfluence : 0 ≤ influence)
    (hpoincare : variance ≤ influence / 4) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  have hsq : t ^ 2 ≤ 256 := by nlinarith
  have hfactor : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    norm_num
    nlinarith
  calc
    variance ≤ (1 / 4 : ℝ) * influence := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hinfluence

/-- Final algebraic combination, leaving only the graph-specific spectral input. -/
theorem variance_large_log_assembly (t ell variance influence lowConstant : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell) (hinfluence : 0 ≤ influence)
    (hlow : lowConstant ≤ 256 / t ^ 2)
    (hvariance : variance ≤ (lowConstant + 8192 / ell ^ 2) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence :=
  hvariance.trans (mul_le_mul_of_nonneg_right
    (variance_constant_assembly t ell lowConstant ht hell hlow) hinfluence)

/-- The spectral variance bound for Fourier coefficients indexed by finite supports. -/
theorem variance_from_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence) :
    variance ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  classical
  let s : Finset (Finset ι) := Finset.univ.filter Finset.Nonempty
  have hdir : (∑ S ∈ s, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence := by
    rw [← hdirichlet]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hSempty : S = ∅ := by simpa [s, Finset.not_nonempty_iff_eq_empty] using hS
    simp [hSempty]
  have hcap : (∑ S ∈ s with (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence := by
    simpa only [s, Finset.filter_filter] using hcapture
  rw [hvariance]
  exact variance_from_spectral_capture s (fun S => coeff S ^ 2)
    (fun S => (S.card : ℝ)) sigma ell influence lowConstant hsigma hell
    (fun S _ => sq_nonneg _) (fun S _ => Nat.cast_nonneg _) hcap hdir

/-- Parseval and the first spectral moment immediately imply Poincaré. -/
theorem variance_le_dirichlet_of_fourier {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance dirichlet : ℝ)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = dirichlet) :
    variance ≤ dirichlet := by
  classical
  rw [hvariance, ← hdirichlet]
  calc
    (∑ S : Finset ι with S.Nonempty, coeff S ^ 2) ≤
        ∑ S : Finset ι with S.Nonempty, (S.card : ℝ) * coeff S ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.mem_filter.mp hS).2
      have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
      nlinarith [sq_nonneg (coeff S)]
    _ ≤ ∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S _ _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- A deliberately generous quadratic-exponential estimate. -/
lemma quadratic_mul_exp_neg_eighth_le (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t / 8) ≤ 256 := by
  have hlin : t / 16 ≤ Real.exp (t / 16) := by
    have h := Real.add_one_le_exp (t / 16)
    linarith
  have hsquare : (t / 16) ^ 2 ≤ (Real.exp (t / 16)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hlin 2
  have hexp : (Real.exp (t / 16)) ^ 2 = Real.exp (t / 8) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsquare
  have hquad : t ^ 2 ≤ 256 * Real.exp (t / 8) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hquad (le_of_lt (Real.exp_pos (-t / 8)))
  have hcancel : Real.exp (t / 8) * Real.exp (-t / 8) = 1 := by
    rw [← Real.exp_add]
    have hzero : t / 8 + -t / 8 = 0 := by ring
    rw [hzero, Real.exp_zero]
  nlinarith [hcancel]

/-- The exponentially small term in the block argument, with ample constant slack. -/
lemma block_exponential_remainder_le (t ell : ℝ) (ht : 0 ≤ t)
    (hell : t / 2 - Real.log 2 ≤ ell) :
    (4 * Real.exp (-ell / 4)) * t ^ 2 ≤ 2048 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have harg : -ell / 4 ≤ Real.log 2 - t / 8 := by linarith
  have hmono : Real.exp (-ell / 4) ≤ 2 * Real.exp (-t / 8) := by
    calc
      Real.exp (-ell / 4) ≤ Real.exp (Real.log 2 + (-t / 8)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 2 * Real.exp (-t / 8) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hquad := quadratic_mul_exp_neg_eighth_le t ht
  have hmul := mul_le_mul_of_nonneg_right hmono (sq_nonneg t)
  nlinarith

/-- A form requiring only the logarithmic lower bound used for the spectral tail. -/
lemma block_exponential_remainder_le_of_third (t ell : ℝ) (ht : 0 ≤ t)
    (hell : t / 3 ≤ ell) :
    (4 * Real.exp (-ell / 4)) * t ^ 2 ≤ 2304 := by
  have hquad := quadratic_mul_exp_neg_eighth_le (2 * t / 3) (by positivity)
  have harg : -(2 * t / 3) / 8 = -t / 12 := by ring
  rw [harg] at hquad
  have hmono : Real.exp (-ell / 4) ≤ Real.exp (-t / 12) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hmono (sq_nonneg t)
  nlinarith

/-- The fractional-power form of the block remainder estimate. -/
lemma block_rpow_remainder_le (t m : ℝ) (ht : 0 ≤ t) (hm : 0 < m)
    (hm_log : t / 3 ≤ Real.log m) :
    (4 * m ^ (-1 / 4 : ℝ)) * t ^ 2 ≤ 2304 := by
  rw [Real.rpow_def_of_pos hm]
  have harg : Real.log m * (-1 / 4 : ℝ) = -Real.log m / 4 := by ring
  rw [harg]
  exact block_exponential_remainder_le_of_third t (Real.log m) ht hm_log

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- The graph-independent final step of the variance proof: capture at squared
logarithmic degree, together with Parseval and the Dirichlet identity, yields
the exact advertised numerical constant. -/
theorem variance_bound_of_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t m : ℝ)
    (hsigma : 0 < sigma) (hinfluence : 0 ≤ influence)
    (ht : 0 < t) (hm : 0 < m) (hlog : t / 3 ≤ Real.log m)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  have hell : 0 < Real.log m := lt_of_lt_of_le (by positivity : 0 < t / 3) hlog
  have hpre := variance_from_fourier_capture coeff variance sigma (Real.log m)
    influence (4 * m ^ (-1 / 4 : ℝ)) hsigma hell hvariance hdirichlet hcapture
  have hrem : 4 * m ^ (-1 / 4 : ℝ) ≤ 2304 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    exact block_rpow_remainder_le t m ht.le hm hlog
  have hconstant := variance_constant_assembly_budget t (Real.log m)
    (4 * m ^ (-1 / 4 : ℝ)) 2304 ht hlog hrem (by norm_num)
  exact hpre.trans (mul_le_mul_of_nonneg_right hconstant hinfluence)

/-- A complete numerical reduction for all logarithmic scales. The only
large-scale input remaining is capture of low Fourier supports. -/
theorem variance_bound_of_fourier_inputs {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma influence t : ℝ)
    (hsigma : 0 < sigma) (hsigma_sq : sigma ^ 2 ≤ 1 / 4)
    (hinfluence : 0 ≤ influence) (ht : 0 < t)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : 16 ≤ t → ∃ m : ℝ, 0 < m ∧ t / 3 ≤ Real.log m ∧
      (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * Real.log m / 64) ^ 2 / 2, coeff S ^ 2)
        ≤ (4 * m ^ (-1 / 4 : ℝ)) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  by_cases hlarge : 16 ≤ t
  · obtain ⟨m, hm, hlog, hcap⟩ := hcapture hlarge
    exact variance_bound_of_fourier_capture coeff variance sigma influence t m
      hsigma hinfluence ht hm hlog hvariance hdirichlet hcap
  · have hpoincare := variance_le_dirichlet_of_fourier coeff variance
      (sigma ^ 2 * influence) hvariance hdirichlet
    have hquarter : variance ≤ influence / 4 := by
      have h := mul_le_mul_of_nonneg_right hsigma_sq hinfluence
      linarith
    exact variance_small_log_assembly t variance influence ht (by linarith)
      hinfluence hquarter

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.BlockAverage

open scoped BigOperators

/-- Exchange the average over blocks with a sum over objects detected by a block. -/
theorem weighted_incidence_sum
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) =
      ∑ s, (∑ b, if P b s then μ b else 0) * w s := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : P b s <;> simp [h]

/-- Nonnegative block weights give nonnegative incidence probabilities. -/
theorem incidence_sum_nonneg
    {β : Type v} [Fintype β] (μ : β → ℝ) (P : β → Prop)
    [DecidablePred P] (hμ : ∀ b, 0 ≤ μ b) :
    0 ≤ ∑ b, if P b then μ b else 0 := by
  apply Finset.sum_nonneg
  intro b hb
  split_ifs
  · exact hμ b
  · exact le_rfl

/-- A collection of nonnegative masses detected with probability at least `c`
contributes at least `c` times its total mass to the average detected mass. -/
theorem capture_lower_bound
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : β → ℝ) (w : α → ℝ) (P : β → α → Prop)
    [DecidableRel P] (low : Finset α) (c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0) :
    c * ∑ s ∈ low, w s ≤ ∑ b, μ b * ∑ s, if P b s then w s else 0 := by
  rw [weighted_incidence_sum, Finset.mul_sum]
  calc
    ∑ s ∈ low, c * w s ≤
        ∑ s ∈ low, (∑ b, if P b s then μ b else 0) * w s := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_right (hcapture s hs) (hw s)
    _ ≤ ∑ s, (∑ b, if P b s then μ b else 0) * w s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
      intro s hs hnot
      exact mul_nonneg (incidence_sum_nonneg μ (fun b => P b s) hμ) (hw s)

/-- Pointwise block bounds average to a global bound using the incidence
probability of each coordinate. No normalization assumption is required. -/
theorem block_upper_bound
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (a d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤ a * d * ∑ i, I i := by
  calc
    (∑ b, μ b * ∑ s, if P b s then w s else 0) ≤
        ∑ b, μ b * (a * ∑ i, if E b i then I i else 0) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hblock b) (hμ b)
    _ = a * ∑ b, μ b * ∑ i, if E b i then I i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = a * ∑ i, (∑ b, if E b i then μ b else 0) * I i := by
      rw [weighted_incidence_sum]
    _ ≤ a * ∑ i, d * I i := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hincidence i) (hI i)
    _ = a * d * ∑ i, I i := by rw [← Finset.mul_sum]; ring

/-- The algebraic block-capture argument, with arbitrary capture and incidence
constants. It separates all finite averaging from the Fourier and graph input. -/
theorem captured_mass_le
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c d : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ d) :
    (∑ s ∈ low, w s) ≤ (a * d / c) * ∑ i, I i := by
  have hlow := capture_lower_bound μ w P low c hμ hw hcapture
  have hupp := block_upper_bound μ w I P E a d hμ hI ha hblock hincidence
  have hcombined := hlow.trans hupp
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * ∑ s ∈ low, w s ≤ a * d * ∑ i, I i := hcombined
    _ = c * ((a * d / c) * ∑ i, I i) := by field_simp [ne_of_gt hc]

/-- The factor-four consequence used for uniform vertex blocks:
capture at least `m/(2*n)` and edge incidence at most `2*m/n`. -/
theorem captured_mass_le_four
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [Fintype β] [Fintype ι]
    (μ : β → ℝ) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hw : ∀ s, 0 ≤ w s)
    (hI : ∀ i, 0 ≤ I i) (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤ ∑ b, if P b s then μ b else 0)
    (hblock : ∀ b, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i, (∑ b, if E b i then μ b else 0) ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by
  have h := captured_mass_le μ w I P E low a c (4 * c)
    hμ hw hI ha hc hcapture hblock hincidence
  have hc0 : c ≠ 0 := ne_of_gt hc
  have heq : a * (4 * c) / c = 4 * a := by field_simp [ne_of_gt hc]
  simpa only [heq] using h

/-- Uniform finite sampling agrees with the normalized cardinality used by the
vertex-block counting lemmas. This also holds for an empty sampling family. -/
theorem uniform_incidence_sum
    {β : Type v} [DecidableEq β] (Ω : Finset β) (P : β → Prop)
    [DecidablePred P] :
    (∑ b : Ω, if P b.val then (1 : ℝ) / Ω.card else 0) =
      ((Ω.filter P).card : ℝ) / Ω.card := by
  rw [← Finset.sum_subtype Ω (fun _ => Iff.rfl)
    (fun b => if P b then (1 : ℝ) / Ω.card else 0)]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Uniform-block version of the factor-four capture argument, stated entirely
with cardinal-ratio probabilities to match the combinatorial counting API. -/
theorem captured_mass_le_four_uniform
    {α : Type u} {β : Type v} {ι : Type w} [Fintype α] [DecidableEq β] [Fintype ι]
    (Ω : Finset β) (w : α → ℝ) (I : ι → ℝ)
    (P : β → α → Prop) (E : β → ι → Prop)
    [DecidableRel P] [DecidableRel E] (low : Finset α) (a c : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hI : ∀ i, 0 ≤ I i)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hcapture : ∀ s ∈ low, c ≤
      ((Ω.filter (fun b => P b s)).card : ℝ) / Ω.card)
    (hblock : ∀ b ∈ Ω, (∑ s, if P b s then w s else 0) ≤
      a * ∑ i, if E b i then I i else 0)
    (hincidence : ∀ i,
      ((Ω.filter (fun b => E b i)).card : ℝ) / Ω.card ≤ 4 * c) :
    (∑ s ∈ low, w s) ≤ 4 * a * ∑ i, I i := by
  apply captured_mass_le_four
    (fun _ : Ω => (1 : ℝ) / Ω.card) w I
    (fun b s => P b.val s) (fun b i => E b.val i) low a c
  · intro b
    positivity
  · exact hw
  · exact hI
  · exact ha
  · exact hc
  · intro s hs
    rw [uniform_incidence_sum Ω (fun b => P b s)]
    exact hcapture s hs
  · intro b
    exact hblock b.val b.property
  · intro i
    rw [uniform_incidence_sum Ω (fun b => E b i)]
    exact hincidence i

end Problem313.BlockAverage

end

end OAI
end
end

section
section
namespace OAI


/-! Finite-product averaging for pivotal influences under restrictions. -/
noncomputable section
open scoped BigOperators

namespace Problem313.RestrictionInfluence

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Bernoulli weight on an arbitrary finite set of coordinates. -/
def weight (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then p else 1 - p

/-- The pivotal influence, with the redundant pivotal coordinate included in the sum. -/
def influence (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x, if f (Function.update x i true) ≠ f (Function.update x i false)
    then weight p x else 0

variable (P : ι → Prop) [DecidablePred P]

/-- Glue a free and an exterior configuration into a full configuration. -/
def join (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) : ι → Bool :=
  fun i => if h : P i then x ⟨i, h⟩ else y ⟨i, h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem join_pos (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) : join P x y i = x i := by
  simp [join, i.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem join_neg (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // ¬ P i}) : join P x y i = y i := by
  simp [join, i.property]

omit [DecidableEq ι] in
/-- Product weights factor across any coordinate partition. -/
theorem weight_join (p : ℝ) (x : {i // P i} → Bool)
    (y : {i // ¬ P i} → Bool) :
    weight p (join P x y) = weight p x * weight p y := by
  unfold weight
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  simp only [join_pos, join_neg]

/-- Fubini for a coordinate restriction, with the exterior sum outermost. -/
theorem sum_weight_join (p : ℝ) (g : (ι → Bool) → ℝ) :
    (∑ z, weight p z * g z) =
      ∑ y : {i // ¬ P i} → Bool, weight p y *
        ∑ x : {i // P i} → Bool, weight p x * g (join P x y) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => Bool)
  rw [← e.symm.sum_comp (fun z => weight p z * g z)]
  change (∑ z : ({i // P i} → Bool) × ({i // ¬ P i} → Bool),
    weight p (join P z.1 z.2) * g (join P z.1 z.2)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [weight_join]
  ring

omit [Fintype ι] in
/-- Updating a free coordinate commutes with gluing an exterior configuration. -/
theorem join_update (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) (b : Bool) :
    join P (Function.update x i b) y = Function.update (join P x y) i.val b := by
  classical
  funext j
  by_cases hji : j = i.val
  · subst j
    simp [join, i.property]
  · by_cases hj : P j
    · have hsub : (⟨j, hj⟩ : {i // P i}) ≠ i := by
        intro h
        exact hji (congrArg Subtype.val h)
      simp [join, hj, hji, hsub]
    · simp [join, hj, hji]

/-- Averaging one pivotal influence over the exterior recovers the full influence. -/
theorem average_influence (p : ℝ) (f : (ι → Bool) → Bool) (i : {i // P i}) :
    (∑ y : {i // ¬ P i} → Bool,
      weight p y * influence p (fun x => f (join P x y)) i) =
        influence p f i.val := by
  classical
  unfold influence
  have h := sum_weight_join P p (fun z =>
    if f (Function.update z i.val true) ≠ f (Function.update z i.val false)
      then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp only [join_update]

/-- Averaging total influence on the free coordinates gives the sum of their original influences. -/
theorem average_totalInfluence (p : ℝ) (f : (ι → Bool) → Bool) :
    (∑ y : {i // ¬ P i} → Bool, weight p y *
      ∑ i : {i // P i}, influence p (fun x => f (join P x y)) i) =
        ∑ i : {i // P i}, influence p f i.val := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => average_influence P p f i)

end Problem313.RestrictionInfluence

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped Classical BigOperators

namespace Problem313

/-- The generic restriction weight agrees with the qualified graph weight. -/
theorem restrictionWeight_eq_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    RestrictionInfluence.weight p x = graphWeight p x := rfl

/-- The generic restriction influence agrees with the qualified graph influence. -/
theorem restrictionInfluence_eq_edgeInfluence {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool) (e : GraphEdge n) :
    RestrictionInfluence.influence p f e = edgeInfluence p f e := rfl

/-- The two generic influence interfaces have definitionally identical weights. -/
theorem restrictionWeight_eq_reindexWeight {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (x : ι → Bool) :
    RestrictionInfluence.weight p x = Reindex.weight p x := rfl

/-- The two generic influence interfaces have equal influences after identifying their decidable-equality instances. -/
theorem restrictionInfluence_eq_reindexInfluence {ι : Type u} [Fintype ι] [d : DecidableEq ι]
    (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    RestrictionInfluence.influence p f i = Reindex.influence p f i := by
  cases Subsingleton.elim d (Classical.typeDecidableEq ι)
  rfl

/-- Averaging a conditional free-edge influence recovers its original graph influence. -/
theorem block_average_edgeInfluence {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (p : ℝ)
    (f : GraphConfig n → Bool) (e : {e : GraphEdge n // EdgeTouches B e}) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      edgeInfluence p f e.val := by
  have h := RestrictionInfluence.average_influence (EdgeTouches B) p f e
  unfold RestrictionInfluence.join at h
  unfold restrictCube pasteCube
  simpa only [← restrictionWeight_eq_reindexWeight,
    ← restrictionInfluence_eq_reindexInfluence,
    ← restrictionInfluence_eq_edgeInfluence] using h

/-- Averaging conditional total influence gives precisely the original influences of
edges touching the block; no invariance or monotonicity is needed. -/
theorem block_average_totalInfluence {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (p : ℝ)
    (f : GraphConfig n → Bool) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * ∑ e : {e : GraphEdge n // EdgeTouches B e},
        Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have h := RestrictionInfluence.average_totalInfluence (EdgeTouches B) p f
  unfold RestrictionInfluence.join at h
  unfold restrictCube pasteCube
  simpa only [← restrictionWeight_eq_reindexWeight,
    ← restrictionInfluence_eq_reindexInfluence,
    ← restrictionInfluence_eq_edgeInfluence] using h

/-- The conditional total-influence identity, with a filtered finite edge sum. -/
theorem block_average_totalInfluence_filter {n : ℕ} (B : Finset (Fin n))
    [DecidablePred (EdgeTouches B)] (p : ℝ) (f : GraphConfig n → Bool) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      Reindex.weight p y * ∑ e : {e : GraphEdge n // EdgeTouches B e},
        Reindex.influence p (restrictCube (EdgeTouches B) f y) e) =
      ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e := by
  rw [block_average_totalInfluence]
  exact (Finset.sum_subtype (Finset.univ.filter (EdgeTouches B))
    (by intro e; simp) (edgeInfluence p f)).symm

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Product Bernoulli weight is unchanged by renaming its coordinates. -/
theorem weight_reindex (e : ι ≃ κ) (p : ℝ) (x : ι → Bool) :
    weight p (Reindex.config e x) = weight p x := by
  unfold weight
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Fourier characters are natural under a bijection of coordinate sets. -/
theorem char_reindex (e : ι ≃ κ) (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    char p (S.map e.toEmbedding) (Reindex.config e x) = char p S x := by
  simp [char, Finset.prod_map]

/-- Every weighted finite expectation is unchanged by coordinate transport. -/
theorem expectation_reindex (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) :
    (∑ y, weight p y * g y) = ∑ x, weight p x * f x := by
  classical
  symm
  apply Fintype.sum_equiv (Reindex.configEquiv e)
  intro x
  simp only [Reindex.configEquiv_apply, weight_reindex, hfg]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Transport of Fourier coefficients, with the support transported by `Finset.map`. -/
theorem coeff_reindex (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) (S : Finset ι) :
    coeff p g (S.map e.toEmbedding) = coeff p f S := by
  classical
  unfold coeff
  symm
  apply Fintype.sum_equiv (Reindex.configEquiv e)
  intro x
  simp only [Reindex.configEquiv_apply, weight_reindex, hfg, char_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Coordinate transport of spectral synthesis, including a degree-dependent multiplier. -/
theorem spectral_sum_reindex (e : ι ≃ κ) (p : ℝ) (M : ℕ → ℝ)
    (c : Finset ι → ℝ) (d : Finset κ → ℝ)
    (hcd : ∀ S, d (S.map e.toEmbedding) = c S) (x : ι → Bool) :
    (∑ T : Finset κ, M T.card * d T * char p T (Reindex.config e x)) =
      ∑ S : Finset ι, M S.card * c S * char p S x := by
  classical
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.card_map, hcd, char_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Spectral noise is natural under arbitrary finite-coordinate equivalences. -/
theorem noise_sum_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) (x : ι → Bool) :
    (∑ T : Finset κ, ρ ^ T.card * coeff p g T * char p T (Reindex.config e x)) =
      ∑ S : Finset ι, ρ ^ S.card * coeff p f S * char p S x := by
  apply spectral_sum_reindex e p (fun k => ρ ^ k)
  exact coeff_reindex e p f g hfg

/-- The fourth-moment hypercontractive statement transports along coordinate equivalences. -/
theorem noise_fourth_moment_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x)
    (hf : (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * coeff p f S * char p S x) ^ 4) ≤
        (∑ x, weight p x * (f x) ^ 2) ^ 2) :
    (∑ y, weight p y *
        (∑ T : Finset κ, ρ ^ T.card * coeff p g T * char p T y) ^ 4) ≤
        (∑ y, weight p y * (g y) ^ 2) ^ 2 := by
  classical
  rw [expectation_reindex e p (fun x =>
    (∑ S : Finset ι, ρ ^ S.card * coeff p f S * char p S x) ^ 4)
    (fun y => (∑ T : Finset κ, ρ ^ T.card * coeff p g T * char p T y) ^ 4)
    (fun x => congrArg (fun z : ℝ => z ^ 4) (noise_sum_reindex e p ρ f g hfg x))]
  rw [expectation_reindex e p (fun x => (f x) ^ 2) (fun y => (g y) ^ 2)
    (fun x => congrArg (fun z : ℝ => z ^ 2) (hfg x))]
  exact hf

/-- A proof of spectral hypercontractivity on every `Fin n` cube suffices for every
finite coordinate type. This isolates the reindexing burden from the product induction. -/
theorem noise_fourth_moment_of_fin (p ρ : ℝ)
    (hfin : ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      (∑ x, weight p x *
        (∑ S : Finset (Fin n), ρ ^ S.card * coeff p f S * char p S x) ^ 4) ≤
        (∑ x, weight p x * (f x) ^ 2) ^ 2)
    (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * coeff p g S * char p S x) ^ 4) ≤
        (∑ x, weight p x * (g x) ^ 2) ^ 2 := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  exact noise_fourth_moment_reindex e p ρ
    (fun x => g (Reindex.config e x)) g (fun _ => rfl) (hfin _ _)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Every degree-weighted squared coefficient sum is invariant under coordinate transport. -/
theorem coefficient_energy_reindex (e : ι ≃ κ) (M : ℕ → ℝ)
    (c : Finset ι → ℝ) (d : Finset κ → ℝ)
    (hcd : ∀ S, d (S.map e.toEmbedding) = c S) :
    (∑ T : Finset κ, M T.card * (d T) ^ 2) =
      ∑ S : Finset ι, M S.card * (c S) ^ 2 := by
  classical
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.card_map, hcd]

/-- The universal coefficient form of hypercontractivity transports along coordinate
bijections. It is the equivalence branch of finite-type induction. -/
theorem synthesis_contraction_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (hι : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4) ≤
        (∑ S : Finset ι, (c S) ^ 2) ^ 2)
    (d : Finset κ → ℝ) :
    (∑ y, weight p y *
        (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4) ≤
        (∑ T : Finset κ, (d T) ^ 2) ^ 2 := by
  classical
  let c : Finset ι → ℝ := fun S => d (S.map e.toEmbedding)
  have he := spectral_sum_reindex e p (fun k => ρ ^ k) c d (fun _ => rfl)
  rw [expectation_reindex e p
    (fun x => (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4)
    (fun y => (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4)
    (fun x => congrArg (fun z : ℝ => z ^ 4) (he x))]
  have hc : (∑ T : Finset κ, (d T) ^ 2) = ∑ S : Finset ι, (c S) ^ 2 := by
    simpa using coefficient_energy_reindex e (fun _ => 1) c d (fun _ => rfl)
  rw [hc]
  exact hι c

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313

variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

omit [Fintype ι] in
/-- The coordinate equivalence from a predicate and its complement is ordinary pasting. -/
theorem config_sumCompl_eq_pasteCube
    (x : {i // P i} → Bool) (y : {i // ¬P i} → Bool) :
    Reindex.config (Equiv.sumCompl P) (Sum.elim x y) = pasteCube P x y := by
  funext i
  by_cases hi : P i <;> simp [Reindex.config, pasteCube, hi]

namespace BiasedFourier

/-- The ambient support obtained by adjoining free and exterior supports. -/
def subtypeSupport (A : Finset {i // P i}) (D : Finset {i // ¬P i}) : Finset ι :=
  (A.disjSum D).map (Equiv.sumCompl P).toEmbedding

/-- Conditional Fourier coefficients on arbitrary coordinate subtypes agree with
full coefficients after Fourier transformation in the exterior coordinates. -/
theorem coeff_restricted_coeff_subtype (p : ℝ) (f : (ι → Bool) → ℝ)
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
      coeff p f (subtypeSupport P A D) := by
  classical
  let F : ({i // P i} ⊕ {i // ¬P i} → Bool) → ℝ :=
    fun z => f (Reindex.config (Equiv.sumCompl P) z)
  have hsplit : ∀ x y, F (Sum.elim x y) = restrictCube P f y x := by
    intro x y
    simp [F, config_sumCompl_eq_pasteCube, restrictCube]
  calc
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
        coeff p (fun y => coeff p (fun x => F (Sum.elim x y)) A) D := by
      simp only [hsplit]
    _ = coeff p F (A.disjSum D) := coeff_restricted_coeff p F A D
    _ = coeff p f (subtypeSupport P A D) :=
      (coeff_reindex (Equiv.sumCompl P) p F f (fun _ => rfl) (A.disjSum D)).symm

/-- Exact squared-coefficient averaging over arbitrary exterior coordinate subtypes. -/
theorem restricted_coeff_sq_average_subtype [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (A : Finset {i // P i}) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      (coeff p (restrictCube P f y) A) ^ 2) =
      ∑ D : Finset {i // ¬P i}, (coeff p f (subtypeSupport P A D)) ^ 2 := by
  classical
  symm
  simpa only [coeff_restricted_coeff_subtype] using
    parseval hp hp1 (fun y => coeff p (restrictCube P f y) A)

/-- Free and exterior support sets give each ambient support exactly once. -/
def subtypeSupportEquiv :
    (Finset {i // P i} × Finset {i // ¬P i}) ≃ Finset ι :=
  Finset.sumEquiv.toEquiv.symm.trans (Equiv.sumCompl P).finsetCongr

omit [Fintype ι] in
@[simp]
theorem subtypeSupportEquiv_apply
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    subtypeSupportEquiv P (A,D) = subtypeSupport P A D := rfl

omit [Fintype ι] in
@[simp]
theorem subtype_subtypeSupport
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    (subtypeSupport P A D).subtype P = A := by
  ext i
  simp [subtypeSupport]

omit [Fintype ι] in
@[simp]
theorem subtype_not_subtypeSupport
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    (subtypeSupport P A D).subtype (fun i => ¬P i) = D := by
  ext i
  simp [subtypeSupport]

/-- Sum over each ambient support by its free and exterior pieces. -/
theorem sum_subtypeSupport [DecidableEq ι] (h : Finset ι → ℝ) :
    (∑ A : Finset {i // P i}, ∑ D : Finset {i // ¬P i}, h (subtypeSupport P A D)) =
      ∑ S : Finset ι, h S := by
  classical
  calc
    _ = ∑ AD : Finset {i // P i} × Finset {i // ¬P i},
        h (subtypeSupport P AD.1 AD.2) :=
      (Fintype.sum_prod_type (fun AD : Finset {i // P i} × Finset {i // ¬P i} =>
        h (subtypeSupport P AD.1 AD.2))).symm
    _ = _ := by
      apply Fintype.sum_equiv (subtypeSupportEquiv P)
      rintro ⟨A,D⟩
      rfl

/-- Exact restriction-mass transport for any statistic of the free support.
There is deliberately no restriction on exterior Fourier degree. -/
theorem restriction_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (L : Finset {i // P i} → ℝ) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by
  classical
  calc
    (∑ y : {i // ¬P i} → Bool, weight p y *
        ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ A : Finset {i // P i}, L A *
        ∑ y : {i // ¬P i} → Bool, weight p y * coeff p (restrictCube P f y) A ^ 2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ A : Finset {i // P i}, ∑ D : Finset {i // ¬P i},
        L A * coeff p f (subtypeSupport P A D) ^ 2 := by
      simp_rw [restricted_coeff_sq_average_subtype P hp hp1, Finset.mul_sum]
    _ = ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by
      simpa only [subtype_subtypeSupport] using
        sum_subtypeSupport P (fun S => L (S.subtype P) * coeff p f S ^ 2)

/-- Exact restricted Fourier mass at any selection of free-coordinate degrees. -/
theorem restriction_mass_subtype_filter [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A ∈ Finset.univ.filter (fun A : Finset {i // P i} => Q A.card),
        coeff p (restrictCube P f y) A ^ 2) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Q (S.filter P).card),
        coeff p f S ^ 2 := by
  classical
  simpa only [Finset.sum_filter, Finset.card_subtype, ite_mul, one_mul, zero_mul] using
    restriction_mass_subtype P hp hp1 f (fun A => if Q A.card then 1 else 0)

/-- The low-degree restriction identity in conditional-sum format. -/
theorem restriction_low_degree_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ) (k : ℝ) :
    (∑ S : Finset ι, if (S.filter P).Nonempty ∧ ((S.filter P).card : ℝ) ≤ k
      then coeff p f S ^ 2 else 0) =
      ∑ y : {i // ¬P i} → Bool, weight p y *
        ∑ A : Finset {i // P i}, if A.Nonempty ∧ (A.card : ℝ) ≤ k
          then coeff p (restrictCube P f y) A ^ 2 else 0 := by
  classical
  simpa only [Finset.sum_filter, Finset.card_pos] using
    (restriction_mass_subtype_filter P hp hp1 f (fun d => 0 < d ∧ (d : ℝ) ≤ k)).symm

end BiasedFourier
end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- Uniform bias-dependent logarithmic bound used in the low-degree estimate. -/
theorem sigma_mul_log_four_div_le_two {σ : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) : σ * Real.log (4 / σ) ≤ 2 := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hinv : 0 < 1 / (2 * σ) := by positivity
  have hloginv := Real.log_le_sub_one_of_pos hinv
  have hlogsplit : Real.log (4 / σ) =
      3 * Real.log 2 + Real.log (1 / (2 * σ)) := by
    rw [Real.log_div (by norm_num) hσne,
      Real.log_div (by norm_num) (by positivity : 2 * σ ≠ 0),
      Real.log_mul (by norm_num) hσne]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      have := Real.log_pow (2 : ℝ) 2
      norm_num at this
      exact this
    rw [hlog4, Real.log_one]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hloginv (le_of_lt hσ)
  have hcancel : σ * (1 / (2 * σ) - 1) = 1 / 2 - σ := by
    field_simp
  rw [hcancel] at hscaled
  rw [hlogsplit]
  nlinarith [mul_le_mul_of_nonneg_left hlog2 (le_of_lt hσ)]

/-- The noise loss has a uniformly small power of the orbit-size parameter. -/
theorem noise_loss_le_rpow {σ m : ℝ} (hσ : 0 < σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) ≤ m ^ (1 / 16 : ℝ) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hlogneg : Real.log (σ / 4) = -Real.log (4 / σ) := by
    rw [Real.log_div hσne (by norm_num), Real.log_div (by norm_num) hσne]
    ring
  rw [Real.rpow_def_of_pos (by positivity : 0 < σ / 4),
    Real.rpow_def_of_pos hmpos]
  apply Real.exp_le_exp.mpr
  rw [hlogneg]
  have hbound := sigma_mul_log_four_div_le_two hσ hσhalf
  have hmul := mul_le_mul_of_nonneg_right hbound hlogm
  nlinarith

/-- Absorb the residual quarter-variance factor and the stronger exponent. -/
theorem sigma_sq_mul_rpow_le {σ m : ℝ} (hσ : 0 ≤ σ)
    (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m) :
    σ ^ 2 * m ^ (-5 / 16 : ℝ) ≤ m ^ (-1 / 4 : ℝ) := by
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  calc
    σ ^ 2 * m ^ (-5 / 16 : ℝ) ≤ 1 * m ^ (-5 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_right hσsq (Real.rpow_nonneg (le_of_lt hmpos) _)
    _ = m ^ (-5 / 16 : ℝ) := one_mul _
    _ ≤ m ^ (-1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm (by norm_num)

/-- An individual influence contributes a small extra factor when total influence is small. -/
theorem influence_three_halves_le {a I m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    (hai : a ≤ I / m) (hI : I ≤ m ^ (1 / 4 : ℝ)) :
    a ^ (3 / 2 : ℝ) ≤ m ^ (-3 / 8 : ℝ) * a := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hpow : m ^ (-3 / 4 : ℝ) * m = m ^ (1 / 4 : ℝ) := by
    calc
      m ^ (-3 / 4 : ℝ) * m = m ^ (-3 / 4 : ℝ) * m ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = m ^ ((-3 / 4 : ℝ) + 1) := (Real.rpow_add hmpos _ _).symm
      _ = m ^ (1 / 4 : ℝ) := by norm_num
  have hratio : I / m ≤ m ^ (-3 / 4 : ℝ) := by
    apply (div_le_iff₀ hmpos).2
    rwa [hpow]
  have hhalf : a ^ (1 / 2 : ℝ) ≤ m ^ (-3 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow ha (hai.trans hratio) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul (le_of_lt hmpos)] at h
    norm_num at h ⊢
    exact h
  have hsplit : a ^ (3 / 2 : ℝ) = a * a ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add_of_nonneg ha (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at h
    exact h
  rw [hsplit, mul_comm (m ^ _) a]
  exact mul_le_mul_of_nonneg_left hhalf ha

/-- Sum the individual three-halves estimate without a cardinality loss. -/
theorem sum_influence_three_halves_le {ι : Type u} (s : Finset ι) (a : ι → ℝ)
    {m : ℝ} (hm : 1 ≤ m) (ha : ∀ i ∈ s, 0 ≤ a i)
    (horbit : ∀ i ∈ s, a i ≤ (∑ j ∈ s, a j) / m)
    (hsmall : (∑ j ∈ s, a j) ≤ m ^ (1 / 4 : ℝ)) :
    (∑ i ∈ s, a i ^ (3 / 2 : ℝ)) ≤ m ^ (-3 / 8 : ℝ) * (∑ i ∈ s, a i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    influence_three_halves_le (ha i hi) hm (horbit i hi) hsmall

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- Summing pivotal-event three-halves powers using a uniform influence bound. -/
theorem sum_mul_sqrt_le {ι : Type u} [Fintype ι] (a : ι → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : ∀ i, a i ≤ B) :
    (∑ i, a i * Real.sqrt (a i)) ≤ Real.sqrt B * ∑ i, a i := by
  calc
    (∑ i, a i * Real.sqrt (a i)) ≤ ∑ i, a i * Real.sqrt B := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hB i)) (ha i)
    _ = Real.sqrt B * ∑ i, a i := by rw [Finset.mul_sum]; congr 1; ext i; ring

/-- A convenient conversion between real three-halves powers and square roots. -/
theorem rpow_three_halves_eq_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3/2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_add_of_nonneg hx (show (0:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) using 1 <;> norm_num

/-- The small-total-influence regime turns the individual influence bound into a power of `m`. -/
theorem sqrt_influence_ratio_le (m I : ℝ) (hm : 0 < m)
    (hI : I ≤ m ^ (1/4 : ℝ)) :
    Real.sqrt (I/m) ≤ m ^ (-3/8 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Real.rpow_nonneg hm.le _, ?_⟩
  have hsq : (m ^ (-3/8 : ℝ))^2 = m ^ (-3/4 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm.le]
    norm_num
  rw [hsq]
  calc
    I/m ≤ m ^ (1/4 : ℝ) / m := div_le_div_of_nonneg_right hI hm.le
    _ = m ^ (-3/4 : ℝ) := by
      convert (Real.rpow_sub hm (1/4 : ℝ) 1).symm using 1 <;> norm_num

/-- The numerical case split at the end of the low-degree Fourier estimate.
The factor `A` can be instantiated with `σ²`. -/
theorem low_degree_influence_bound {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hL1 : L ≤ 1)
    (hprojection : L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hI0 : 0 ≤ I := by rw [← hsum]; exact Finset.sum_nonneg fun i _ => ha i
  have hpow0 : 0 ≤ m ^ (1/16 : ℝ) := Real.rpow_nonneg hmpos.le _
  by_cases hsmall : I ≤ m ^ (1/4 : ℝ)
  · have hsum_bound : (∑ i, (a i) ^ (3/2 : ℝ)) ≤ m ^ (-3/8 : ℝ) * I := by
      calc
        (∑ i, (a i) ^ (3/2 : ℝ)) = ∑ i, a i * Real.sqrt (a i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact rpow_three_halves_eq_mul_sqrt (a i) (ha i)
        _ ≤ Real.sqrt (I/m) * I := by
          simpa [hsum] using sum_mul_sqrt_le a (I/m) ha hindividual
        _ ≤ m ^ (-3/8 : ℝ) * I := mul_le_mul_of_nonneg_right
          (sqrt_influence_ratio_le m I hmpos hsmall) hI0
    have hcoefficient : A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) ≤ m ^ (-1/4 : ℝ) := by
      calc
        A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) ≤
            m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using mul_le_mul_of_nonneg_right hA1 hpow0)
            (Real.rpow_nonneg hmpos.le _)
        _ = m ^ (-5/16 : ℝ) := by rw [← Real.rpow_add hmpos]; norm_num
        _ ≤ m ^ (-1/4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
    calc
      L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ) := hprojection
      _ ≤ A * m ^ (1/16 : ℝ) * (m ^ (-3/8 : ℝ) * I) :=
        mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg hA0 hpow0)
      _ = (A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ)) * I := by ring
      _ ≤ m ^ (-1/4 : ℝ) * I := mul_le_mul_of_nonneg_right hcoefficient hI0
  · have hinverse : m ^ (-1/4 : ℝ) * m ^ (1/4 : ℝ) = 1 := by
      rw [← Real.rpow_add hmpos]
      norm_num
    calc
      L ≤ 1 := hL1
      _ = m ^ (-1/4 : ℝ) * m ^ (1/4 : ℝ) := hinverse.symm
      _ ≤ m ^ (-1/4 : ℝ) * I := mul_le_mul_of_nonneg_left
        (le_of_lt (lt_of_not_ge hsmall)) (Real.rpow_nonneg hmpos.le _)

/-- Version accepting the hypercontractive factor before its power bound is substituted. -/
theorem low_degree_influence_bound_of_factor {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A R L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hR : R ≤ m ^ (1/16 : ℝ)) (hL1 : L ≤ 1)
    (hprojection : L ≤ A * R * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  apply low_degree_influence_bound a m I A L hm ha hsum hindividual hA0 hA1 hL1
  exact hprojection.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR hA0)
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _))

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

open Finset

/-- Every nonempty low-degree Fourier support is counted by at least one of
its incident coordinate sums.  This is purely finite, nonnegative double counting. -/
theorem lowDegree_mass_le_incident_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k : ℝ) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro S hS
  by_cases h : S.Nonempty ∧ (S.card : ℝ) ≤ k
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h.1
    calc
      a S = (if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) := by simp [hi, h.2]
      _ ≤ ∑ j : ι, if j ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by
        apply Finset.single_le_sum (f := fun j : ι =>
          if j ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) (s := Finset.univ)
        · intro j hj
          split_ifs
          · exact ha S
          · exact le_refl 0
        · exact Finset.mem_univ i
  · rw [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact ha S
    · exact le_refl 0

/-- Assemble coordinatewise low-degree estimates without any choice of a
single coordinate common to all supports. -/
theorem lowDegree_mass_le_of_coordinate_bound
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k C : ℝ)
    (J : ι → ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι,
      if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤ C * J i) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ i : ι, J i := by
  calc
    _ ≤ ∑ i : ι, ∑ S : Finset ι,
        if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 :=
      lowDegree_mass_le_incident_mass a ha k
    _ ≤ ∑ i : ι, C * J i := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = C * ∑ i : ι, J i := (Finset.mul_sum _ _ _).symm

/-- A cutoff below one contains no nonconstant Boolean Fourier supports. -/
theorem lowDegree_mass_eq_zero_of_lt_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) {k : ℝ} (hk : k < 1) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  apply ite_eq_right
  rintro ⟨hne, hcard⟩
  have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast hne.card_pos
  linarith

/-- Erasing a fixed coordinate injects supports containing it into supports
of no larger degree.  This transports a derivative coefficient identity to
a low-degree mass bound, without changing the ambient coordinate type. -/
theorem incident_mass_le_erase_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a b : Finset ι → ℝ) (hb : ∀ T, 0 ≤ b T) (i : ι) (k C : ℝ)
    (hC : 0 ≤ C)
    (hderiv : ∀ S, i ∈ S → a S = C * b (S.erase i)) :
    (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ T : Finset ι, if (T.card : ℝ) ≤ k then b T else 0 := by
  let s : Finset (Finset ι) := univ.filter (fun S => i ∈ S ∧ (S.card : ℝ) ≤ k)
  let t : Finset (Finset ι) := univ.filter (fun T => (T.card : ℝ) ≤ k)
  have hinj : Set.InjOn (fun S : Finset ι => S.erase i) (s : Set (Finset ι)) := by
    intro S hS T hT hST
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2.1
    have hiT : i ∈ T := (Finset.mem_filter.mp hT).2.1
    simpa only [Finset.insert_erase hiS, Finset.insert_erase hiT] using
      congrArg (fun U : Finset ι => insert i U) hST
  have hsub : s.image (fun S => S.erase i) ⊆ t := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcard : ((S.erase i).card : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_erase_le (s := S) (a := i)
    exact hcard.trans (Finset.mem_filter.mp hS).2.2
  calc
    _ = ∑ S ∈ s, a S := (Finset.sum_filter _ _).symm
    _ = ∑ S ∈ s, C * b (S.erase i) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hderiv S (Finset.mem_filter.mp hS).2.1
    _ = C * ∑ S ∈ s, b (S.erase i) := (Finset.mul_sum _ _ _).symm
    _ = C * ∑ T ∈ s.image (fun S => S.erase i), b T := by
      rw [Finset.sum_image hinj]
    _ ≤ C * ∑ T ∈ t, b T := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => hb T)
    _ = _ := by rw [Finset.sum_filter]

/-- The complete low-degree estimate once the analytic Fourier ingredients
are supplied: the derivative coefficient identity and the low-degree
projection bound.  All incidence counting, bias constants, and the
small/large total-influence split are discharged here. -/
theorem lowDegree_bound_of_projection
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (b : ι → Finset ι → ℝ) (J : ι → ℝ)
    (σ m : ℝ) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m)
    (ha : ∀ S, 0 ≤ a S) (hb : ∀ i S, 0 ≤ b i S)
    (hJ : ∀ i, 0 ≤ J i) (horbit : ∀ i, J i ≤ (∑ j, J j) / m)
    (henergy : (∑ S : Finset ι, a S) ≤ 1)
    (hderiv : ∀ i S, i ∈ S → a S = σ ^ 2 * b i (S.erase i))
    (hprojection : ∀ i,
      (∑ S : Finset ι, if (S.card : ℝ) ≤ σ * Real.log m / 64 then b i S else 0) ≤
        (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) * (J i) ^ (3 / 2 : ℝ)) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ σ * Real.log m / 64 then a S else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, J i := by
  let k : ℝ := σ * Real.log m / 64
  let R : ℝ := (σ / 4) ^ (-(2 : ℝ) * k)
  let L : ℝ := ∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0
  have hL1 : L ≤ 1 := by
    apply le_trans _ henergy
    apply Finset.sum_le_sum
    intro S hS
    split_ifs
    · exact le_refl _
    · exact ha S
  have hcoord : ∀ i,
      (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
        (σ ^ 2 * R) * (J i) ^ (3 / 2 : ℝ) := by
    intro i
    calc
      _ ≤ σ ^ 2 * ∑ S : Finset ι, if (S.card : ℝ) ≤ k then b i S else 0 :=
        incident_mass_le_erase_mass a (b i) (hb i) i k (σ ^ 2)
          (sq_nonneg σ) (hderiv i)
      _ ≤ σ ^ 2 * (R * (J i) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hprojection i) (sq_nonneg σ)
      _ = _ := by ring
  have hproj : L ≤ σ ^ 2 * R * ∑ i, (J i) ^ (3 / 2 : ℝ) :=
    lowDegree_mass_le_of_coordinate_bound a ha k (σ ^ 2 * R)
      (fun i => (J i) ^ (3 / 2 : ℝ)) hcoord
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith
  exact low_degree_influence_bound_of_factor J m (∑ i, J i) (σ ^ 2) R L
    hm hJ rfl horbit (sq_nonneg σ) hσsq (noise_loss_le_rpow hσ hσhalf hm) hL1 hproj

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.WeightedProjection

open scoped BigOperators

variable {ι : Type u} {X : Type v} [Fintype X]

def coefficient (w : X → ℝ) (basis : ι → X → ℝ) (f : X → ℝ) (i : ι) : ℝ :=
  ∑ x, w x * f x * basis i x

def synthesis (basis : ι → X → ℝ) (L : Finset ι) (c : ι → ℝ) (x : X) : ℝ :=
  ∑ i ∈ L, c i * basis i x

/-- Pairing a function with a finite spectral expansion pairs its coefficients. -/
theorem inner_synthesis (w : X → ℝ) (basis : ι → X → ℝ)
    (f : X → ℝ) (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * f x * synthesis basis L c x) =
      ∑ i ∈ L, c i * coefficient w basis f i := by
  simp only [synthesis, coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Orthonormality computes the coefficient of a finite spectral expansion. -/
theorem coefficient_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) (i : ι) :
    coefficient w basis (synthesis basis L c) i = if i ∈ L then c i else 0 := by
  unfold coefficient synthesis
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (j : ι) :
      (∑ x, w x * (c j * basis j x) * basis i x) =
        c j * (if j = i then 1 else 0) := by
    rw [← horth j i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp only [hterm]
  simp

/-- The squared norm of a finite orthonormal expansion is its coefficient energy. -/
theorem second_moment_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * (synthesis basis L c x) ^ 2) = ∑ i ∈ L, (c i) ^ 2 := by
  have hid := inner_synthesis w basis (synthesis basis L c) L c
  simp only [coefficient_synthesis w basis horth] at hid
  calc
    (∑ x, w x * (synthesis basis L c x) ^ 2) =
        ∑ x, w x * synthesis basis L c x * synthesis basis L c x := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ i ∈ L, c i * (if i ∈ L then c i else 0) := hid
    _ = ∑ i ∈ L, (c i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi, pow_two]

/-- A spectral projection has the same inner product with the original function
as its squared norm. -/
theorem inner_projection (w : X → ℝ) (basis : ι → X → ℝ)
    (f : X → ℝ) (L : Finset ι) :
    (∑ x, w x * f x * synthesis basis L (coefficient w basis f) x) =
      ∑ i ∈ L, (coefficient w basis f i) ^ 2 := by
  rw [inner_synthesis]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Problem313.WeightedProjection

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

open scoped BigOperators

/-- Removing a diagonal noise multiplier costs at most `rho ^ (-2*k)`
in squared coefficient norm on coefficients supported in degrees at most `k`. -/
theorem inverse_noise_energy_le {ι : Type u} [Fintype ι]
    (degree : ι → ℕ) (c : ι → ℝ) (rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ i, (rho ^ (-(degree i : ℝ)) * c i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hc : c i = 0
  · simp [hc]
  have hexp : -2 * k ≤ -(degree i : ℝ) * 2 := by
    linarith [hdegree i hc]
  have hrpow := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 hexp
  have hsq : (rho ^ (-(degree i : ℝ))) ^ 2 =
      rho ^ (-(degree i : ℝ) * 2) := by
    rw [Real.rpow_mul hrho.le, Real.rpow_two]
  rw [mul_pow, hsq]
  exact mul_le_mul_of_nonneg_right hrpow (sq_nonneg (c i))

/-- Spectral inversion turns a diagonal-noise `L² → L⁴` estimate into an
`L⁴` estimate for a low-degree expansion.  This version is independent of
any particular construction of the orthonormal basis. -/
theorem lowDegree_fourth_of_noise
    {ι : Type u} {X : Type v} [Fintype ι] [Fintype X]
    (degree : ι → ℕ) (basis : ι → X → ℝ) (weight : X → ℝ)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : ι → ℝ,
      (∑ x, weight x * (∑ i, rho ^ (degree i : ℝ) * a i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2)
    (c : ι → ℝ) (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by
  let a : ι → ℝ := fun i => rho ^ (-(degree i : ℝ)) * c i
  have hinv (i : ι) : rho ^ (degree i : ℝ) * a i = c i := by
    dsimp [a]
    rw [← mul_assoc, ← Real.rpow_add hrho]
    simp
  have hnoise' :
      (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2 := by
    simpa only [hinv] using hnoise a
  have henergy : (∑ i, (a i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 :=
    inverse_noise_energy_le degree c rho k hrho hrho1 hdegree
  have hnonneg : 0 ≤ ∑ i, (a i) ^ 2 := by positivity
  have hsq : (∑ i, (a i) ^ 2) ^ 2 ≤
      (rho ^ (-2 * k) * ∑ i, (c i) ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg henergy 2
  have hscale : (rho ^ (-2 * k) * ∑ i, (c i) ^ 2) ^ 2 =
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul hrho.le]
    congr 1
    ring
  exact hnoise'.trans (hsq.trans_eq hscale)

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
namespace Problem313

/-- Weighted finite Hölder inequality with conjugate exponents `4/3` and `4`.
Weights need not be normalized. -/
theorem weighted_holder_four_thirds {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * v i * u i| ≤
      (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∑ i, w i * u i ^ 4) ^ (1 / 4 : ℝ) := by
  classical
  have hpq : Real.HolderConjugate (4 / 3 : ℝ) 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun i => w i ^ (3 / 4 : ℝ) * |v i|)
    (g := fun i => w i ^ (1 / 4 : ℝ) * |u i|) hpq
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (abs_nonneg _))
  have hleft : (∑ i, (w i ^ (3 / 4 : ℝ) * |v i|) *
      (w i ^ (1 / 4 : ℝ) * |u i|)) = ∑ i, w i * |v i| * |u i| := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (w i ^ (3 / 4 : ℝ) * w i ^ (1 / 4 : ℝ)) * |v i| * |u i| := by ring
      _ = w i * |v i| * |u i| := by
        rw [← Real.rpow_add' (hw i) (by norm_num : (3 / 4 : ℝ) + 1 / 4 ≠ 0)]
        norm_num
  have hfirst : (∑ i, (w i ^ (3 / 4 : ℝ) * |v i|) ^ (4 / 3 : ℝ)) =
      ∑ i, w i * |v i| ^ (4 / 3 : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
      ← Real.rpow_mul (hw i)]
    norm_num
  have hsecond : (∑ i, (w i ^ (1 / 4 : ℝ) * |u i|) ^ (4 : ℝ)) =
      ∑ i, w i * u i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
      ← Real.rpow_mul (hw i)]
    have habs : |u i| ^ (4 : ℕ) = u i ^ 4 := by
      rcases le_total 0 (u i) with hi | hi
      · rw [abs_of_nonneg hi]
      · rw [abs_of_nonpos hi]
        ring
    norm_num [Real.rpow_natCast, habs]
  rw [hleft, hfirst, hsecond] at h
  norm_num at h
  refine (Finset.abs_sum_le_sum_abs (fun i => w i * v i * u i) Finset.univ).trans ?_
  simpa only [abs_mul, abs_of_nonneg (hw _)] using h

/-- The scalar cancellation behind the `L⁴` duality argument. -/
theorem projection_moment_bound {M V H A : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hdual : M ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ))
    (hfour : H ≤ A ^ 4 * M ^ 2) :
    M ≤ A ^ 2 * V ^ (3 / 2 : ℝ) := by
  have hroot : H ^ (1 / 4 : ℝ) ≤ A * M ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (A ^ 4 * M ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hH hfour (by norm_num)
      _ = A * M ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (pow_nonneg hA _) (sq_nonneg M),
          ← Real.rpow_natCast_mul hA, ← Real.rpow_natCast_mul hM]
        norm_num
  have hv : 0 ≤ V ^ (3 / 4 : ℝ) := Real.rpow_nonneg hV _
  have hs : 0 ≤ M ^ (1 / 2 : ℝ) := Real.rpow_nonneg hM _
  have hs2 : (M ^ (1 / 2 : ℝ)) ^ 2 = M := by
    rw [← Real.rpow_mul_natCast hM]
    norm_num
  have hbound : M ≤ (A * V ^ (3 / 4 : ℝ)) * M ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ) := hdual
      _ ≤ V ^ (3 / 4 : ℝ) * (A * M ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hroot hv
      _ = _ := by ring
  have hsbound : M ^ (1 / 2 : ℝ) ≤ A * V ^ (3 / 4 : ℝ) := by
    nlinarith [mul_nonneg hA hv]
  have hsq := pow_le_pow_left₀ hs hsbound 2
  have hv2 : (V ^ (3 / 4 : ℝ)) ^ 2 = V ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hV]
    norm_num
  simpa only [hs2, mul_pow, hv2] using hsq

/-- A low-degree fourth-moment bound implies the dual projection estimate.
The hypothesis `hproj` is the usual orthogonal-projection identity
`⟨v,u⟩ = ⟨u,u⟩`; this formulation avoids choosing a normalized dual vector. -/
theorem weighted_projection_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (A : ℝ) (hA : 0 ≤ A)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤ A ^ 4 * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      A ^ 2 * (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  have hM : 0 ≤ ∑ i, w i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hV : 0 ≤ ∑ i, w i * |v i| ^ (4 / 3 : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hH : 0 ≤ ∑ i, w i * u i ^ 4 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)
  apply projection_moment_bound hM hV hH hA _ hfour
  have h := weighted_holder_four_thirds w v u hw
  simpa only [hproj, abs_of_nonneg hM] using h

/-- Dual projection estimate for functions taking their values in `{-1,0,1}`,
as Boolean coordinate differences do. -/
theorem weighted_projection_pivotal_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤ A ^ 4 * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      A ^ 2 * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by
  classical
  have hnorm : (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) =
      ∑ i, if v i ≠ 0 then w i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rcases hv i with hi | hi | hi <;> simp [hi]
  simpa only [hnorm] using weighted_projection_bound w v u hw A hA hproj hfour

/-- The exponent form used for low-degree projections of Boolean derivatives. -/
theorem weighted_projection_noise_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (ρ d : ℝ) (hρ : 0 ≤ ρ)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤
      ρ ^ (-4 * d) * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      ρ ^ (-2 * d) * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by
  have hfourpow : (ρ ^ (-d)) ^ (4 : ℕ) = ρ ^ (-4 * d) := by
    rw [← Real.rpow_mul_natCast hρ]
    congr 1
    ring
  have htwopow : (ρ ^ (-d)) ^ (2 : ℕ) = ρ ^ (-2 * d) := by
    rw [← Real.rpow_mul_natCast hρ]
    congr 1
    ring
  have h := weighted_projection_pivotal_bound w v u hw hv (ρ ^ (-d))
    (Real.rpow_nonneg hρ _) hproj (by simpa only [hfourpow] using hfour)
  simpa only [htwopow] using h

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The projection onto the specified finite collection of Fourier characters. -/
def project (p : ℝ) (L : Finset (Finset ι))
    (g : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ S ∈ L, coeff p g S * char p S x

/-- Pairing a function with its projection gives its selected Fourier energy. -/
theorem project_inner (p : ℝ) (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by
  classical
  unfold project
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  calc
    (∑ x, weight p x * g x * (coeff p g S * char p S x)) =
        coeff p g S * (∑ x, weight p x * g x * char p S x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (coeff p g S) ^ 2 := by
      change coeff p g S * coeff p g S = (coeff p g S) ^ 2
      ring

/-- The squared norm of a Fourier projection is its selected Fourier energy. -/
theorem project_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (project p L g x) ^ 2) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by
  classical
  simpa only [project, WeightedProjection.synthesis] using
    WeightedProjection.second_moment_synthesis (weight p) (char p)
      (char_inner_product hp hp1) L (coeff p g)

/-- The defining orthogonality identity needed by the projection/Hölder estimate. -/
theorem project_inner_eq_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ x, weight p x * (project p L g x) ^ 2 := by
  rw [project_inner, project_second_moment hp hp1]

/-- Specialization of inverse-noise hypercontractivity to the canonical Fourier
projection.  The hypothesis is precisely the coefficient-form noise estimate. -/
theorem project_fourth_moment_of_noise (p rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ x, weight p x * (project p L g x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ S ∈ L, (coeff p g S) ^ 2) ^ 2 := by
  classical
  let c : Finset ι → ℝ := fun S => if S ∈ L then coeff p g S else 0
  have hdegree' : ∀ S, c S ≠ 0 → (S.card : ℝ) ≤ k := by
    intro S hc
    by_cases hS : S ∈ L
    · exact hdegree S hS
    · simp [c, hS] at hc
  have hnoise' : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ (S.card : ℝ) * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2 := by
    intro a
    simpa only [Real.rpow_natCast] using hnoise a
  have hbound := Problem313.lowDegree_fourth_of_noise Finset.card (char p)
    (weight p) rho k hrho hrho1 hnoise' c hdegree'
  have hsynth (x : ι → Bool) : (∑ S, c S * char p S x) = project p L g x := by
    simp [c, project, ite_mul, Finset.sum_ite_mem]
  have henergy : (∑ S, (c S) ^ 2) = ∑ S ∈ L, (coeff p g S) ^ 2 := by
    simp [c, ite_pow, Finset.sum_ite_mem]
  simpa only [hsynth, henergy] using hbound

/-- The concrete Fourier projection estimate for ternary-valued functions,
including Boolean coordinate differences. -/
theorem project_energy_le_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 0 ∨ g x = 1)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p g S) ^ 2) ≤
      rho ^ (-2 * k) *
        (∑ x, if g x ≠ 0 then weight p x else 0) ^ (3 / 2 : ℝ) := by
  have hw (x : ι → Bool) : 0 ≤ weight p x := by
    unfold weight
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarWeight
    split_ifs <;> linarith
  have hfour := project_fourth_moment_of_noise p rho k hrho hrho1 hnoise L g hdegree
  have hbound := Problem313.weighted_projection_noise_bound (weight p) g (project p L g)
    hw hg rho k hrho.le (project_inner_eq_second_moment hp hp1 L g)
    (by simpa only [project_second_moment hp hp1] using hfour)
  simpa only [project_second_moment hp hp1] using hbound

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- Low-degree projection bound for a Boolean coordinate difference, with the
pivotal probability expressed by the shared generic influence definition. -/
theorem booleanDifference_project_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (f : (ι → Bool) → Bool) (i : ι)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p
      (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by
  let g : (ι → Bool) → ℝ := fun x =>
    boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))
  have hg (x : ι → Bool) : g x = -1 ∨ g x = 0 ∨ g x = 1 := by
    cases ht : f (Function.update x i true) <;>
      cases hf : f (Function.update x i false) <;> simp [g, ht, hf, boolReal]
  have hpiv : (∑ x, if g x ≠ 0 then weight p x else 0) =
      Reindex.influence p f i := by
    unfold Reindex.influence
    apply Finset.sum_congr rfl
    intro x hx
    cases ht : f (Function.update x i true) <;>
      cases hf : f (Function.update x i false) <;>
        simp [g, ht, hf, boolReal, weight, scalarWeight, Reindex.weight]
  simpa only [hpiv] using
    project_energy_le_of_noise hp hp1 rho k hrho hrho1 hnoise L g hg hdegree

/-- The Boolean coordinate-difference energy bound with a real degree cutoff. -/
theorem booleanDifference_lowDegree_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (f : (ι → Bool) → Bool) (i : ι) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι => (S.card : ℝ) ≤ k),
      (coeff p (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by
  apply booleanDifference_project_energy_le hp hp1 rho k hrho hrho1 hnoise _ f i
  intro S hS
  exact (Finset.mem_filter.mp hS).2

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators
open Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Separate the new coordinate from the product Bernoulli weight. -/
theorem weight_option (p : ℝ) (x : Option ι → Bool) :
    weight p x = scalarWeight p (x none) * weight p (fun i => x (some i)) := by
  simp only [weight, Fintype.prod_option]

@[simp] theorem weight_option_elim (p : ℝ) (b : Bool) (x : ι → Bool) :
    weight p ((fun i : Option ι => Option.elim i b x)) = scalarWeight p b * weight p x := by
  rw [weight_option]
  rfl

/-- Exact expectation splitting at the distinguished `none` coordinate.
This identity is polynomial and requires no restriction on the bias. -/
theorem weighted_sum_option (p : ℝ) (g : (Option ι → Bool) → ℝ) :
    (∑ x, weight p x * g x) =
      (1 - p) * (∑ y, weight p y * g ((fun i : Option ι => Option.elim i false y))) +
        p * (∑ y, weight p y * g ((fun i : Option ι => Option.elim i true y))) := by
  let e : (Option ι → Bool) ≃ Bool × (ι → Bool) := Equiv.piOptionEquivProd
  rw [← e.symm.sum_comp (fun x => weight p x * g x), Fintype.sum_prod_type,
    Fintype.sum_bool]
  have he (b : Bool) (y : ι → Bool) : e.symm (b, y) = (fun i : Option ι => Option.elim i b y) := by
    funext i
    cases i <;> rfl
  simp_rw [he, weight_option_elim, scalarWeight_true, scalarWeight_false,
    mul_assoc, ← Finset.mul_sum]
  ring

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.BiasedFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The scalar hypercontractive estimate in normalized character notation. -/
theorem scalar_synthesis_fourth {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : ℝ) :
    (1 - p) * (a + (Real.sqrt (p * (1-p)) / 4) * chi p false * b) ^ 4 +
      p * (a + (Real.sqrt (p * (1-p)) / 4) * chi p true * b) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos hp (sub_pos.mpr hp1)))
  have hfalse : (Real.sqrt (p * (1-p)) / 4) * chi p false = -p / 4 := by
    rw [chi_false]
    field_simp
  have htrue : (Real.sqrt (p * (1-p)) / 4) * chi p true = (1-p) / 4 := by
    rw [chi_true]
    field_simp
  rw [hfalse, htrue]
  convert Problem313.biased_two_point_fourth_moment p a b hp.le hp1.le using 1; ring

/-- Tensorization step for an additional Boolean coordinate, in spectral form. -/
theorem synthesis_fourth_option_of_split {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hsplit : ∀ g : (Option ι → Bool) → ℝ,
      (∑ x, weight p x * g x) =
        (1-p) * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t false y)) +
        p * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t true y)))
    (ih : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2)
    (c : Finset (Option ι) → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by
  classical
  let ρ := Real.sqrt (p*(1-p))/4
  let c₀ : Finset ι → ℝ := fun S => c (S.map Function.Embedding.some)
  let c₁ : Finset ι → ℝ := fun S => c (Finset.insertNone S)
  let A : (ι → Bool) → ℝ := fun x => ∑ S, ρ ^ S.card * c₀ S * char p S x
  let B : (ι → Bool) → ℝ := fun x => ∑ S, ρ ^ S.card * c₁ S * char p S x
  have hw : ∀ x : ι → Bool, 0 ≤ weight p x := by
    intro x
    apply Finset.prod_nonneg
    intro i hi
    cases x i <;> simp [scalarWeight] <;> linarith
  have hA : (∑ x, weight p x * (A x) ^ 4) ≤ (∑ S, c₀ S ^ 2) ^ 2 := ih c₀
  have hB : (∑ x, weight p x * (B x) ^ 4) ≤ (∑ S, c₁ S ^ 2) ^ 2 := ih c₁
  have hbound := Problem313.weighted_fourth_moment_add_sq Finset.univ
    (weight p) A B (∑ S, c₀ S ^ 2) (∑ S, c₁ S ^ 2)
    (fun x _ => hw x) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hA hB
  rw [coefficient_energy_option]
  change _ ≤ ((∑ S, c₀ S ^ 2) + ∑ S, c₁ S ^ 2) ^ 2
  calc
    _ = (1-p) * (∑ x, weight p x * (A x + ρ * chi p false * B x) ^ 4) +
        p * (∑ x, weight p x * (A x + ρ * chi p true * B x) ^ 4) := by
      rw [hsplit]
      simp only [synthesis_option]
      rfl
    _ = ∑ x, weight p x * ((1-p) * (A x + ρ * chi p false * B x) ^ 4 +
        p * (A x + ρ * chi p true * B x) ^ 4) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ x, weight p x * ((A x) ^ 2 + (B x) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (scalar_synthesis_fourth hp hp1 (A x) (B x)) (hw x)
    _ ≤ _ := hbound

/-- Initial case of the finite-coordinate tensorization induction. -/
theorem synthesis_fourth_empty {ι : Type u} [Fintype ι] [IsEmpty ι]
    (p : ℝ) (c : Finset ι → ℝ) :
    (∑ x : ι → Bool, weight p x *
      (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card * c S * char p S x) ^ 4) ≤
      (∑ S, c S ^ 2) ^ 2 := by
  have he : (default : Finset ι) = ∅ := Subsingleton.elim _ _
  simp [weight, char, he]
  ring_nf
  exact le_rfl

/-- Biased product hypercontractivity in its root-free, arbitrary-coefficient form. -/
theorem synthesis_fourth_bound {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : Finset ι → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by
  classical
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ c : Finset α → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2) ?_ ?_ ?_ ι c
  · intro α β _ e h d
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact synthesis_contraction_reindex e p (Real.sqrt (p*(1-p))/4) h d
  · exact synthesis_fourth_empty p
  · intro α _ h d
    convert! synthesis_fourth_option_of_split hp hp1 (weighted_sum_option p) h d using 1
    apply Finset.sum_congr (by ext x; simp)
    intro x hx
    rfl

/-- The noise operator contracts the weighted second moment into the fourth moment. -/
theorem noise_fourth_bound {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      coeff p g S * char p S x) ^ 4) ≤ (∑ x, weight p x * (g x) ^ 2) ^ 2 := by
  have h := synthesis_fourth_bound hp hp1 (coeff p g)
  rw [parseval hp hp1 g] at h
  exact h

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The biased low-degree influence estimate, with the product noise
contraction as its only remaining analytic premise. -/
theorem low_degree_estimate_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, (Real.sqrt (p * (1 - p)) / 4) ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  have hvar : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hσ : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hvar
  have hσhalf : Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (p - 1 / 2)]
  have hρ : 0 < Real.sqrt (p * (1 - p)) / 4 := by positivity
  have hρ1 : Real.sqrt (p * (1 - p)) / 4 ≤ 1 := by linarith
  refine lowDegree_bound_of_projection
    (fun S => coeff p (fun x => boolReal (f x)) S ^ 2)
    (fun i S => coeff p (delta i (fun x => boolReal (f x))) S ^ 2)
    (Reindex.influence p f) (Real.sqrt (p * (1 - p))) m hσ hσhalf hm
    (fun S => sq_nonneg _) (fun i S => sq_nonneg _)
    (Reindex.influence_nonneg hp.le hp1.le f) horbit
    (boolean_spectral_mass_le_one hp hp1 f) ?_ ?_
  · intro i S hi
    rw [Real.sq_sqrt hvar.le]
    exact coeff_sq_eq_variance_mul_delta_erase_sq hp hp1
      (fun x => boolReal (f x)) i S hi
  · intro i
    change (∑ S : Finset ι,
      if (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S ^ 2 else 0) ≤ _
    simpa only [Finset.sum_filter] using
      booleanDifference_lowDegree_energy_le hp hp1
        (Real.sqrt (p * (1 - p)) / 4)
        (Real.sqrt (p * (1 - p)) * Real.log m / 64)
        hρ hρ1 hnoise f i

/-- Version of the low-degree estimate written as a filtered sum with the
literal positive integer degree condition. -/
theorem low_degree_estimate_filter_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, (Real.sqrt (p * (1 - p)) / 4) ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι =>
      1 ≤ S.card ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64),
      coeff p (fun x => boolReal (f x)) S ^ 2) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  simpa only [Finset.sum_filter, Finset.one_le_card] using
    low_degree_estimate_of_noise hp hp1 f m hm horbit hnoise

/-- The biased Boolean low-degree estimate.  No monotonicity or symmetry
is required beyond the displayed bound on each coordinate influence. -/
theorem low_degree_estimate {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  exact low_degree_estimate_of_noise hp hp1 f m hm horbit
    (synthesis_fourth_bound hp hp1)

/-- The literal integer-degree filtered-sum form of the low-degree estimate. -/
theorem low_degree_estimate_filter {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι =>
      1 ≤ S.card ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64),
      coeff p (fun x => boolReal (f x)) S ^ 2) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  exact low_degree_estimate_filter_of_noise hp hp1 f m hm horbit
    (synthesis_fourth_bound hp hp1)

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators

namespace Problem313

/-- Averaging the low-degree estimate over exterior configurations preserves its
linear influence bound.  This is the fixed-block averaging step, before averaging
in the choice of the vertex block. -/
theorem average_conditional_low_degree_bound
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P]
    (p k C : ℝ) (f : (ι → Bool) → Bool)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hbound : ∀ y : {i // ¬ P i} → Bool,
      (∑ A : Finset {i // P i},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p
            (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
        else 0) ≤
      C * ∑ i : {i // P i}, RestrictionInfluence.influence p
        (fun x => f (RestrictionInfluence.join P x y)) i) :
    (∑ y : {i // ¬ P i} → Bool, BiasedFourier.weight p y *
      ∑ A : Finset {i // P i},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p
            (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
        else 0) ≤
      C * ∑ i : {i // P i}, RestrictionInfluence.influence p f i.val := by
  classical
  have hw (y : {i // ¬ P i} → Bool) : 0 ≤ BiasedFourier.weight p y := by
    apply Finset.prod_nonneg
    intro i hi
    unfold BiasedFourier.scalarWeight
    split_ifs <;> linarith
  calc
    _ ≤ ∑ y : {i // ¬ P i} → Bool, BiasedFourier.weight p y *
        (C * ∑ i : {i // P i}, RestrictionInfluence.influence p
          (fun x => f (RestrictionInfluence.join P x y)) i) := by
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hbound y) (hw y))
    _ = C * ∑ y : {i // ¬ P i} → Bool, RestrictionInfluence.weight p y *
        ∑ i : {i // P i}, RestrictionInfluence.influence p
          (fun x => f (RestrictionInfluence.join P x y)) i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      change BiasedFourier.weight p y * (C * _) =
        C * (BiasedFourier.weight p y * _)
      ring
    _ = _ := by rw [RestrictionInfluence.average_totalInfluence]

/-- The same averaging step with the original Fourier mass supplied by the exact
restriction identity. Both premises are equalities/inequalities about the actual
canonical product cube, not an abstract replacement for graph probability. -/
theorem original_mass_bound_of_conditional
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P]
    (p k C M : ℝ) (f : (ι → Bool) → Bool)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hmass : M =
      ∑ y : {i // ¬ P i} → Bool, BiasedFourier.weight p y *
        ∑ A : Finset {i // P i},
          if A.Nonempty ∧ (A.card : ℝ) ≤ k then
            BiasedFourier.coeff p
              (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
          else 0)
    (hbound : ∀ y : {i // ¬ P i} → Bool,
      (∑ A : Finset {i // P i},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p
            (fun x => boolReal (f (RestrictionInfluence.join P x y))) A ^ 2
        else 0) ≤
      C * ∑ i : {i // P i}, RestrictionInfluence.influence p
        (fun x => f (RestrictionInfluence.join P x y)) i) :
    M ≤ C * ∑ i : {i // P i}, RestrictionInfluence.influence p f i.val := by
  rw [hmass]
  exact average_conditional_low_degree_bound P p k C f hp hp1 hbound

/-- The conditional influence premise for the low-degree theorem follows from
vertex invariance and the low-degree estimate on the restricted cube. -/
theorem block_conditional_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
      BiasedFourier.weight p y *
        ∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
          if A.Nonempty ∧ (A.card : ℝ) ≤ k then
            BiasedFourier.coeff p
              (fun x => boolReal (restrictCube (EdgeTouches B) f y x)) A ^ 2
          else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have hb (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool) :=
    hestimate (restrictCube (EdgeTouches B) f y)
      (fun e => block_restricted_influence_le B hB f hf hp hp1 y e)
  calc
    _ ≤ ∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
        Reindex.weight p y *
          (C * ∑ e, Reindex.influence p (restrictCube (EdgeTouches B) f y) e) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hb y) (Reindex.weight_nonneg hp hp1 y)
    _ = C * ∑ y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool,
        Reindex.weight p y *
          ∑ e, Reindex.influence p (restrictCube (EdgeTouches B) f y) e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [block_average_totalInfluence]

/-- Fixed-block Fourier estimate: all exterior Fourier degrees are retained.
The only analytic input is the ordinary low-degree estimate on the free cube. -/
theorem block_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ S : Finset (GraphEdge n),
      if (S.filter (EdgeTouches B)).Nonempty ∧
          ((S.filter (EdgeTouches B)).card : ℝ) ≤ k then
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  rw [BiasedFourier.restriction_low_degree_mass_subtype (EdgeTouches B) hp hp1]
  exact block_conditional_low_degree_bound_of_estimate B hB f hf p k C
    hp.le hp1.le hestimate

/-- The fixed-block low-degree Fourier bound for invariant graph properties.
All symmetry, restriction and analytic premises are discharged. -/
theorem block_low_degree_bound
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset (GraphEdge n),
      if (S.filter (EdgeTouches B)).Nonempty ∧
          ((S.filter (EdgeTouches B)).card : ℝ) ≤
            Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64 then
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (B.card : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have hm : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
  exact block_low_degree_bound_of_estimate B hB f hf p
    (Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64)
    ((B.card : ℝ) ^ (-1 / 4 : ℝ)) hp hp1
    (fun g hg => BiasedFourier.low_degree_estimate hp hp1 g (B.card : ℝ) hm hg)

/-- Filtered finite-sum version of the fixed-block low-degree bound. -/
theorem block_low_degree_bound_filter
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
      1 ≤ (S.filter (EdgeTouches B)).card ∧
        ((S.filter (EdgeTouches B)).card : ℝ) ≤
          Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64),
      BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (B.card : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e := by
  have h := block_low_degree_bound B hB f hf hp hp1
  have hs : (∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val) =
      ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e :=
    (Finset.sum_subtype (Finset.univ.filter (EdgeTouches B))
      (by intro e; simp) (edgeInfluence p f)).symm
  rw [hs] at h
  simpa only [Finset.sum_filter, Finset.one_le_card] using h

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem313

/-- The fixed-block Fourier estimate and the pointwise support-capture estimate
combine into the global captured-mass bound. All graph sampling probabilities
are the canonical `blockProbability`; the edge-touch bound is discharged here.
The two hypotheses are precisely the analytic and combinatorial inputs, with
no requirement that a single block capture every support simultaneously. -/
theorem graph_fourier_capture_of_block_bounds
    {n m : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hmn : m ≤ n)
    (k a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ S : Finset (GraphEdge n), S.Nonempty →
      (S.card : ℝ) ≤ k ^ 2 / 2 →
      (m : ℝ) / (2 * n) ≤
        blockProbability (Finset.univ : Finset (Fin n)) m (fun B =>
          1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k))
    (hblock : ∀ B : Finset (Fin n), B.card = m →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * a * totalInfluence p f := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard m
  let low := (Finset.univ : Finset (Finset (GraphEdge n))).filter
    (fun S => S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2)
  let mass := fun S : Finset (GraphEdge n) =>
    BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2
  let detect := fun (B : Finset (Fin n)) (S : Finset (GraphEdge n)) =>
    1 ≤ (S.filter (EdgeTouches B)).card ∧
      ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
  have hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < (m : ℝ) / (2 * n) := by positivity
  have hcap : ∀ S ∈ low,
      (m : ℝ) / (2 * n) ≤
        ((Ω.filter (fun B => detect B S)).card : ℝ) / Ω.card := by
    intro S hS
    obtain ⟨_, hSne, hScard⟩ := Finset.mem_filter.mp hS
    simpa only [blockProbability_eq] using hcapture S hSne hScard
  have hb : ∀ B ∈ Ω,
      (∑ S, if detect B S then mass S else 0) ≤
        a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0 := by
    intro B hB
    exact hblock B (Finset.mem_powersetCard.mp hB).2
  have hi : ∀ e : GraphEdge n,
      ((Ω.filter (fun B => EdgeTouches B e)).card : ℝ) / Ω.card ≤
        4 * ((m : ℝ) / (2 * n)) := by
    intro e
    have htouch := blockProbability_edge_touch_le
      (Finset.univ : Finset (Fin n)) e.val (Finset.subset_univ _) e.property hm
      (by simpa using hmn)
    have hevent : blockProbability (Finset.univ : Finset (Fin n)) m
        (fun B => EdgeTouches B e) =
        blockProbability (Finset.univ : Finset (Fin n)) m
          (fun B => (B ∩ e.val).Nonempty) := by
      apply blockProbability_congr
      intro B hB
      simp only [EdgeTouches, Finset.Nonempty, Finset.mem_inter]
      exact exists_congr (fun _ => and_comm)
    change blockProbability (Finset.univ : Finset (Fin n)) m
      (fun B => EdgeTouches B e) ≤ _
    rw [hevent]
    calc
      _ ≤ (2 : ℝ) * m / (Finset.univ : Finset (Fin n)).card := htouch
      _ = 4 * ((m : ℝ) / (2 * n)) := by simp; ring
  have h := BlockAverage.captured_mass_le_four_uniform Ω mass
    (edgeInfluence p f) detect EdgeTouches low a ((m : ℝ) / (2 * n))
    (fun S => sq_nonneg _) (edgeInfluence_nonneg hp hp1 f) ha hc hcap hb hi
  simpa only [low, mass, Finset.sum_filter, totalInfluence] using h

/-- At the square-root block size all counting and numerical capture premises
are discharged. Only the fixed-block analytic estimate remains as input. -/
theorem graph_fourier_captured_mass_of_block_bound
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ))
    (hp : 0 < p) (hp1 : p < 1)
    (hblock : ∀ B : Finset (Fin n), B.card = ⌊Real.sqrt (n : ℝ)⌋₊ →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤
              Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by
  have hm := sqrt_block_size_bounds n hn ht
  apply graph_fourier_capture_of_block_bounds f hp.le hp1.le
    (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega) hm.2.1
    (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64)
    ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) (by positivity)
  · intro S hS hcard
    have hsigma1 : Real.sqrt (p * (1 - p)) ≤ (1 / 2 : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · nlinarith [sq_nonneg (p - 1 / 2)]
    have hdet := sqrt_block_detection_probability n (Real.sqrt (p * (1 - p)))
      hn ht (Real.sqrt_nonneg _) hsigma1 S hS hcard
    refine hdet.trans_eq ?_
    apply blockProbability_congr
    intro B hB
    simp only [BlockDetects, edgeTouches_iff_not_disjoint]
  · exact hblock

/-- The complete captured Fourier-mass bound for a vertex-invariant graph
property. The bias is unrestricted within `(0,1)` and no monotonicity is used. -/
theorem graph_fourier_captured_mass
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ)) (hf : VertexInvariant f)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by
  apply graph_fourier_captured_mass_of_block_bound f hn ht hp hp1
  intro B hB
  have hBm : 3 ≤ B.card := by
    rw [hB]
    exact (sqrt_block_size_bounds n hn ht).1
  simpa only [hB, Finset.sum_filter] using
    block_low_degree_bound_filter B hBm f hf hp hp1

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- The graph-level variance reduction, with the two spectral identities and
large-scale block capture supplied explicitly. No symmetry is needed after
these inputs have been obtained. -/
theorem graphVariance_bound_of_spectral_inputs {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hvariance : graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2)
    (hdirichlet : (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) =
      p * (1 - p) * totalInfluence p f)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  classical
  have hbias : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hsigma : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 hbias
  have hsigma_sq : Real.sqrt (p * (1 - p)) ^ 2 ≤ 1 / 4 := by
    rw [Real.sq_sqrt hbias.le]
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  apply variance_bound_of_fourier_inputs
    (BiasedFourier.coeff p (fun x => boolReal (f x)))
    (graphVariance p f) (Real.sqrt (p * (1 - p)))
    (totalInfluence p f) (Real.log (n : ℝ))
    hsigma hsigma_sq (totalInfluence_nonneg hp.le hp1.le f) hlog hvariance
  · simpa only [Real.sq_sqrt hbias.le] using hdirichlet
  · intro ht
    refine ⟨(⌊Real.sqrt (n : ℝ)⌋₊ : ℝ), ?_, log_sqrt_block_lower n hn ht, hcapture ht⟩
    have hm := (sqrt_block_size_bounds n hn ht).1
    exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊)

/-- Parseval discharges the variance identity, leaving the Dirichlet and captured-mass inputs. -/
theorem graphVariance_bound_of_dirichlet_capture {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hdirichlet : (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) =
      p * (1 - p) * totalInfluence p f)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact graphVariance_bound_of_spectral_inputs f p hn hp hp1
    (graphVariance_eq_fourier_sum_nonempty hp hp1 f) hdirichlet hcapture

/-- All spectral and numerical ingredients are discharged; only the graph-specific
large-scale captured-mass estimate remains. -/
theorem graphVariance_bound_of_capture {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact graphVariance_bound_of_dirichlet_capture f p hn hp hp1
    (graph_fourier_dirichlet hp hp1 f) hcapture

/-- The graph variance bound, with all spectral, analytic, counting, and
numerical inputs discharged. -/
theorem variance_influence_bound_core
    (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ)
    (hn : 2 ≤ n) (hf : VertexInvariant f) (hp : 0 < p) (hp1 : p < 1) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  classical
  apply graphVariance_bound_of_capture f p hn hp hp1
  intro ht
  simpa only [Finset.sum_filter] using
    graph_fourier_captured_mass f hn ht hf hp hp1

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- Removing one specified coordinate injects supports containing it into the
set of supports of no larger degree. This is the finite-sum step behind the
low-degree derivative estimate. -/
theorem sum_squares_le_derivative_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (L : Finset (Finset ι)) (c : Finset ι → ℝ)
    (d : ι → Finset ι → ℝ) (σ k : ℝ) (i : ι)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k)
    (hcoeff : ∀ A : Finset ι, i ∉ A → c (insert i A) = σ * d i A) :
    (∑ S ∈ L.filter (fun S => i ∈ S), c S ^ 2) ≤
      σ ^ 2 * ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => (A.card : ℝ) ≤ k), d i A ^ 2 := by
  classical
  let T := L.filter (fun S => i ∈ S)
  let U := (Finset.univ : Finset (Finset ι)).filter (fun A => (A.card : ℝ) ≤ k)
  have hT : ∀ S ∈ T, i ∈ S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hinj : Set.InjOn (fun S : Finset ι => S.erase i) (T : Set (Finset ι)) := by
    intro S hS R hR h
    have h' := congrArg (insert i) h
    simpa [Finset.insert_erase (hT S hS), Finset.insert_erase (hT R hR)] using h'
  have hsub : T.image (fun S => S.erase i) ⊆ U := by
    intro A hA
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcard : ((S.erase i).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset i S)
    exact hcard.trans (hdegree S (Finset.mem_filter.mp hS).1)
  have heq : (∑ S ∈ T, c S ^ 2) =
      σ ^ 2 * ∑ A ∈ T.image (fun S => S.erase i), d i A ^ 2 := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hc := hcoeff (S.erase i) (Finset.notMem_erase i S)
    rw [Finset.insert_erase (hT S hS)] at hc
    rw [hc]
    ring
  change (∑ S ∈ T, c S ^ 2) ≤ σ ^ 2 * ∑ A ∈ U, d i A ^ 2
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => sq_nonneg (d i A))

/-- Every nonempty support is counted by at least one coordinate. Combining
this double counting with the insertion identity bounds its Fourier mass by
the sum of the low-degree masses of all coordinate derivatives. -/
theorem low_degree_derivative_counting
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (L : Finset (Finset ι)) (c : Finset ι → ℝ)
    (d : ι → Finset ι → ℝ) (σ k : ℝ)
    (hne : ∀ S ∈ L, S.Nonempty)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k)
    (hcoeff : ∀ (i : ι) (A : Finset ι), i ∉ A → c (insert i A) = σ * d i A) :
    (∑ S ∈ L, c S ^ 2) ≤
      σ ^ 2 * ∑ i : ι, ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => (A.card : ℝ) ≤ k), d i A ^ 2 := by
  classical
  have hcount : (∑ S ∈ L, c S ^ 2) ≤
      ∑ i : ι, ∑ S ∈ L.filter (fun S => i ∈ S), c S ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro S hS
    obtain ⟨i, hi⟩ := hne S hS
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun j => if j ∈ S then c S ^ 2 else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
    simpa [hi] using h
  calc
    (∑ S ∈ L, c S ^ 2) ≤
        ∑ i : ι, ∑ S ∈ L.filter (fun S => i ∈ S), c S ^ 2 := hcount
    _ ≤ ∑ i : ι, σ ^ 2 * ∑ A ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun A => (A.card : ℝ) ≤ k), d i A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_squares_le_derivative_sum L c d σ k i hdegree (hcoeff i)
    _ = _ := by rw [Finset.mul_sum]

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- The numerical part of the biased low-degree estimate, with its original noise loss. -/
theorem low_degree_bound_of_noise_projection {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I σ L : ℝ)
    (hm : 1 ≤ m) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = I)
    (hindividual : ∀ i, a i ≤ I / m) (hL1 : L ≤ 1)
    (hprojection : L ≤ σ ^ 2 * (σ / 4) ^
      (-(2 : ℝ) * (σ * Real.log m / 64)) * ∑ i, (a i) ^ (3 / 2 : ℝ)) :
    L ≤ m ^ (-1 / 4 : ℝ) * I := by
  apply low_degree_influence_bound a m I (σ ^ 2) L hm ha hsum hindividual
    (sq_nonneg σ) (by nlinarith) hL1
  apply hprojection.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (noise_loss_le_rpow hσ hσhalf hm) (sq_nonneg σ)
  · exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _

/-- The Bernoulli standard deviation lies in the range required by the noise estimate. -/
theorem bernoulli_stddev_bounds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) ∧ Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
  constructor
  · exact Real.sqrt_pos.2 (mul_pos hp (sub_pos.2 hp1))
  · apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    nlinarith [sq_nonneg (p - 1 / 2)]

/-- Bias-parameter form of the numerical low-degree estimate. -/
theorem low_degree_bound_of_biased_projection {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I p L : ℝ)
    (hm : 1 ≤ m) (hp : 0 < p) (hp1 : p < 1)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = I)
    (hindividual : ∀ i, a i ≤ I / m) (hL1 : L ≤ 1)
    (hprojection : L ≤ (p * (1 - p)) * (Real.sqrt (p * (1 - p)) / 4) ^
      (-(2 : ℝ) * (Real.sqrt (p * (1 - p)) * Real.log m / 64)) *
      ∑ i, (a i) ^ (3 / 2 : ℝ)) :
    L ≤ m ^ (-1 / 4 : ℝ) * I := by
  obtain ⟨hσ, hσhalf⟩ := bernoulli_stddev_bounds hp hp1
  apply low_degree_bound_of_noise_projection a m I (Real.sqrt (p * (1 - p))) L
    hm hσ hσhalf ha hsum hindividual hL1
  simpa only [Real.sq_sqrt (le_of_lt (mul_pos hp (sub_pos.2 hp1)))] using hprojection

end Problem313

end

end OAI
end
end

section
section
/-! Numerical and incidence estimates for low Fourier degrees. -/
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313.NoiseKernel

variable {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]

omit [Fintype α] in
/-- The subset-indexed spectral kernel factors coordinatewise. -/
theorem spectral_kernel (ρ : ℝ) (φ : ι → α → ℝ) (x y : α) :
    (∑ S : Finset ι, ρ ^ S.card * (∏ i ∈ S, φ i x) * (∏ i ∈ S, φ i y)) =
      ∏ i, (1 + ρ * φ i x * φ i y) := by
  classical
  rw [Finset.prod_one_add]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.prod_mul_distrib, Finset.prod_const]

/-- A spectral multiplier by `ρ ^ |S|` is the corresponding weighted
product-kernel operator. No orthogonality hypotheses are needed for this
algebraic identity. -/
theorem spectral_eq_kernel (ρ : ℝ) (φ : ι → α → ℝ) (w g : α → ℝ) (x : α) :
    (∑ S : Finset ι, ρ ^ S.card *
      (∑ y, w y * g y * (∏ i ∈ S, φ i y)) * (∏ i ∈ S, φ i x)) =
    ∑ y, w y * g y * ∏ i, (1 + ρ * φ i x * φ i y) := by
  classical
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← spectral_kernel ρ φ x y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

end Problem313.NoiseKernel

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313

/-- A nonnegative weight which is constant on a sufficiently large finite set
is at most the total weight divided by the size lower bound. -/
theorem weight_le_sum_div_of_constant_on
    {ι : Type u} [Fintype ι] (w : ι → ℝ) (O : Finset ι) (e : ι) (m : ℝ)
    (hm : 0 < m) (hw : ∀ j, 0 ≤ w j)
    (hcard : m ≤ (O.card : ℝ))
    (hconstant : ∀ j ∈ O, w j = w e) :
    w e ≤ (∑ j, w j) / m := by
  classical
  apply (le_div_iff₀ hm).2
  have hsum : ∑ j ∈ O, w j = (O.card : ℝ) * w e := by
    calc
      ∑ j ∈ O, w j = ∑ _j ∈ O, w e := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hconstant j hj
      _ = (O.card : ℝ) * w e := by simp
  have hle : ∑ j ∈ O, w j ≤ ∑ j, w j :=
    Finset.sum_le_univ_sum_of_nonneg hw
  have hmul := mul_le_mul_of_nonneg_right hcard (hw e)
  nlinarith

/-- The same bound when each point of a finite injectively indexed family has
weight equal to the distinguished point. This form avoids constructing an orbit. -/
theorem weight_le_sum_div_of_injective_family
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (e : ι) (φ : κ → ι) (hφ : Function.Injective φ)
    (m : ℝ) (hm : 0 < m) (hcard : m ≤ (Fintype.card κ : ℝ))
    (hw : ∀ j, 0 ≤ w j) (hconstant : ∀ j, w (φ j) = w e) :
    w e ≤ (∑ j, w j) / m := by
  classical
  apply weight_le_sum_div_of_constant_on w (Finset.univ.image φ) e m hm hw
  · simpa [Finset.card_image_of_injective _ hφ] using hcard
  · intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact hconstant k

end Problem313

end

end OAI
end
end

section
section
namespace OAI


/-! Reindexing real-valued expectations and Dirichlet energies on finite Boolean products. -/
noncomputable section
open scoped BigOperators

namespace Problem313.Reindex

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A coordinate equivalence preserves each weighted real-valued expectation. -/
theorem sum_weight_config (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) :
    (∑ y, weight p y * g y) = ∑ x, weight p x * f x := by
  classical
  apply Eq.symm
  apply Fintype.sum_equiv (configEquiv e)
  intro x
  simp only [configEquiv_apply, weight_config, hfg]

/-- The squared energy at a single coordinate is preserved by reindexing. -/
theorem coordinate_energy_config
    (e : ι ≃ κ) (p : ℝ) (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) (i : ι) :
    (∑ y, weight p y *
      (g (Function.update y (e i) true) - g (Function.update y (e i) false)) ^ 2) =
      ∑ x, weight p x *
        (f (Function.update x i true) - f (Function.update x i false)) ^ 2 := by
  apply sum_weight_config e p
  intro x
  simp only [← config_update, hfg]

/-- The full Dirichlet energy is invariant under a finite coordinate equivalence. -/
theorem energy_config
    (e : ι ≃ κ) (p : ℝ) (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) :
    (∑ j, ∑ y, weight p y *
      (g (Function.update y j true) - g (Function.update y j false)) ^ 2) =
      ∑ i, ∑ x, weight p x *
        (f (Function.update x i true) - f (Function.update x i false)) ^ 2 := by
  apply Eq.symm
  apply Fintype.sum_equiv e
  intro i
  exact (coordinate_energy_config e p f g hfg i).symm

/-- Centered second moments are invariant, for any specified center. -/
theorem centered_sum_config (e : ι ≃ κ) (p c : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) :
    (∑ y, weight p y * (g y - c) ^ 2) =
      ∑ x, weight p x * (f x - c) ^ 2 := by
  apply sum_weight_config e p
  intro x
  rw [hfg]

end Problem313.Reindex

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} {M : Type w} [Fintype ι] [Fintype κ] [AddCommMonoid M]

/-- Reindex all Fourier supports on a sum coordinate set by their two parts. -/
theorem sum_support_disjSum (a : Finset (ι ⊕ κ) → M) :
    (∑ S : Finset (ι ⊕ κ), a S) =
      ∑ A : Finset ι, ∑ D : Finset κ, a (A.disjSum D) := by
  classical
  rw [← Fintype.sum_prod_type (fun AD : Finset ι × Finset κ => a (AD.1.disjSum AD.2))]
  exact ((Finset.sumEquiv (α := ι) (β := κ)).toEquiv.symm.sum_comp a).symm

/-- Restricting the free-coordinate support commutes with the support split. -/
theorem sum_support_condition_disjSum (a : Finset (ι ⊕ κ) → M)
    (P : Finset ι → Prop) [DecidablePred P] :
    (∑ S : Finset (ι ⊕ κ), if P S.toLeft then a S else 0) =
      ∑ A : Finset ι, if P A then
        ∑ D : Finset κ, a (A.disjSum D) else 0 := by
  classical
  rw [sum_support_disjSum]
  simp only [Finset.toLeft_disjSum, Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Filter formulation of the same identity, useful for degree cutoffs. -/
theorem sum_support_filter_disjSum (a : Finset (ι ⊕ κ) → M)
    (P : Finset ι → Prop) [DecidablePred P] :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (ι ⊕ κ) => P S.toLeft), a S) =
      ∑ A ∈ Finset.univ.filter P, ∑ D : Finset κ, a (A.disjSum D) := by
  classical
  simp only [Finset.sum_filter]
  exact sum_support_condition_disjSum a P

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Exact averaging of any selected family of conditional Fourier levels. -/
theorem restricted_mass_average {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (L : Finset (Finset ι)) :
    (∑ y : κ → Bool, weight p y *
      ∑ A ∈ L, (coeff p (fun x => f (Sum.elim x y)) A) ^ 2) =
      ∑ A ∈ L, ∑ D : Finset κ, (coeff p f (A.disjSum D)) ^ 2 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  exact restricted_coeff_sq_average hp hp1 f A

/-- The restriction identity reindexed by full supports. The condition is
placed only on the free-coordinate part, never on exterior Fourier degree. -/
theorem restricted_mass_condition {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (P : Finset ι → Prop) [DecidablePred P] :
    (∑ y : κ → Bool, weight p y *
      ∑ A : Finset ι, if P A then
        (coeff p (fun x => f (Sum.elim x y)) A) ^ 2 else 0) =
      ∑ S : Finset (ι ⊕ κ), if P S.toLeft then (coeff p f S) ^ 2 else 0 := by
  classical
  calc
    _ = ∑ A : Finset ι, if P A then
        ∑ D : Finset κ, (coeff p f (A.disjSum D)) ^ 2 else 0 := by
      simpa only [Finset.sum_filter] using
        restricted_mass_average hp hp1 f (Finset.univ.filter P)
    _ = _ := (sum_support_condition_disjSum (fun S => (coeff p f S) ^ 2) P).symm

/-- Literal real-valued conditional degree cutoff, including the case `k < 1`. -/
theorem restricted_low_degree_mass_average {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (k : ℝ) :
    (∑ y : κ → Bool, weight p y *
      ∑ A : Finset ι, if 1 ≤ A.card ∧ (A.card : ℝ) ≤ k then
        (coeff p (fun x => f (Sum.elim x y)) A) ^ 2 else 0) =
      ∑ S : Finset (ι ⊕ κ), if 1 ≤ S.toLeft.card ∧ (S.toLeft.card : ℝ) ≤ k then
        (coeff p f S) ^ 2 else 0 := by
  classical
  exact restricted_mass_condition hp hp1 f (fun A => 1 ≤ A.card ∧ (A.card : ℝ) ≤ k)

end Problem313.BiasedFourier

end

end OAI
end
end

section
section
/-!
Finite-product restriction identities: exact Fourier mass averaging,
coordinate transport, and pivotal-influence averaging.
-/
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- A continuous strictly increasing distribution on the unit interval attains
its infimum-defined quantiles at unique interior points. -/
theorem quantile_attainment_of_strictMonoOn
    {μ : ℝ → ℝ} (hcont : ContinuousOn μ (Set.Icc 0 1))
    (hmono : StrictMonoOn μ (Set.Icc 0 1))
    (hzero : μ 0 = 0) (hone : μ 1 = 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    let q := sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}
    q ∈ Set.Ioo (0 : ℝ) 1 ∧ μ q = a := by
  have ha : a ∈ Set.Icc (μ 0) (μ 1) := by
    rw [hzero, hone]
    exact ⟨ha0.le, ha1.le⟩
  obtain ⟨r, hr, hra⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont ha
  have hr0 : 0 < r := by
    by_contra h
    have heq : r = 0 := le_antisymm (le_of_not_gt h) hr.1
    rw [heq, hzero] at hra
    linarith
  have hr1 : r < 1 := by
    by_contra h
    have heq : r = 1 := le_antisymm hr.2 (le_of_not_gt h)
    rw [heq, hone] at hra
    linarith
  have hset : {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} = Set.Icc r 1 := by
    ext p
    constructor
    · rintro ⟨hp, hap⟩
      refine ⟨?_, hp.2⟩
      by_contra h
      have hlt := hmono hp hr (lt_of_not_ge h)
      rw [hra] at hlt
      exact (not_lt_of_ge hap) hlt
    · intro hp
      have hpunit : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.trans hp.1, hp.2⟩
      refine ⟨hpunit, ?_⟩
      rw [← hra]
      exact hmono.monotoneOn hr hpunit hp.1
  dsimp only
  rw [hset, csInf_Icc hr.2]
  exact ⟨⟨hr0, hr1⟩, hra⟩

/-- Positive derivatives in the interior imply the strict monotonicity required
by the quantile attainment theorem; endpoints only require continuity. -/
theorem strictMonoOn_unit_of_hasDerivAt_pos
    {μ D : ℝ → ℝ} (hcont : ContinuousOn μ (Set.Icc 0 1))
    (hderiv : ∀ p ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt μ (D p) p)
    (hpos : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < D p) :
    StrictMonoOn μ (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont
  intro p hp
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hp
  rw [(hderiv p hp').deriv]
  exact hpos p hp'

/-- The quantile width estimate in derivative form. -/
theorem quantile_attainment_of_hasDerivAt_pos
    {μ D : ℝ → ℝ} (hcont : ContinuousOn μ (Set.Icc 0 1))
    (hderiv : ∀ p ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt μ (D p) p)
    (hpos : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < D p)
    (hzero : μ 0 = 0) (hone : μ 1 = 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    let q := sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}
    q ∈ Set.Ioo (0 : ℝ) 1 ∧ μ q = a :=
  quantile_attainment_of_strictMonoOn hcont
    (strictMonoOn_unit_of_hasDerivAt_pos hcont hderiv hpos) hzero hone ha0 ha1

end Problem313

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem313.RestrictionMass

open scoped BigOperators

/-- Parseval for a finite orthonormal family, with an explicit real weight. -/
theorem weighted_sum_sq_expansion
    {B : Type u} {Y : Type v} [Fintype B] [DecidableEq B] [Fintype Y]
    (w : Y → ℝ) (χ : B → Y → ℝ)
    (horth : ∀ b d, (∑ y, w y * χ b y * χ d y) = if b = d then 1 else 0)
    (c : B → ℝ) :
    (∑ y, w y * (∑ b, c b * χ b y) ^ 2) = ∑ b, c b ^ 2 := by
  classical
  calc
    (∑ y, w y * (∑ b, c b * χ b y) ^ 2) =
        ∑ y, ∑ b, ∑ d, c b * c d * (w y * χ b y * χ d y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ b, ∑ d, c b * c d * (∑ y, w y * χ b y * χ d y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ b, c b ^ 2 := by
      simp [horth, pow_two]

/-- Averaging the squared restricted coefficients eliminates exterior Fourier
cross terms. No sign or normalization assumption on `w` is needed here. -/
theorem average_restriction_mass
    {A : Type w} {B : Type u} {Y : Type v} [Fintype B] [DecidableEq B] [Fintype Y]
    (w : Y → ℝ) (χ : B → Y → ℝ)
    (horth : ∀ b d, (∑ y, w y * χ b y * χ d y) = if b = d then 1 else 0)
    (c : A → B → ℝ) (L : Finset A) :
    (∑ y, w y * ∑ a ∈ L, (∑ b, c a b * χ b y) ^ 2) =
      ∑ a ∈ L, ∑ b, c a b ^ 2 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact weighted_sum_sq_expansion w χ horth (c a)

/-- The same identity with restricted coefficients supplied as a separate function. -/
theorem average_restriction_mass_of_expansion
    {A : Type w} {B : Type u} {Y : Type v} [Fintype B] [DecidableEq B] [Fintype Y]
    (w : Y → ℝ) (χ : B → Y → ℝ)
    (horth : ∀ b d, (∑ y, w y * χ b y * χ d y) = if b = d then 1 else 0)
    (c : A → B → ℝ) (r : A → Y → ℝ)
    (hr : ∀ a y, r a y = ∑ b, c a b * χ b y) (L : Finset A) :
    (∑ y, w y * ∑ a ∈ L, r a y ^ 2) = ∑ a ∈ L, ∑ b, c a b ^ 2 := by
  simp_rw [hr]
  exact average_restriction_mass w χ horth c L

end Problem313.RestrictionMass

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

def unitQuantile (μ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}

theorem unitQuantile_set_bddBelow (μ : ℝ → ℝ) (a : ℝ) :
    BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
  ⟨0, fun _ hp => hp.1.1⟩

theorem unitQuantile_set_nonempty {μ : ℝ → ℝ} {a : ℝ}
    (h1 : μ 1 = 1) (ha : a ≤ 1) :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}.Nonempty := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
  simpa only [h1] using ha

theorem unitQuantile_mem {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h1 : μ 1 = 1) (ha : a ≤ 1) :
    unitQuantile μ a ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ (unitQuantile μ a) := by
  have hc : IsClosed {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
    isClosed_Icc.inter (isClosed_le continuous_const hμ)
  exact hc.csInf_mem (unitQuantile_set_nonempty h1 ha) (unitQuantile_set_bddBelow μ a)

theorem unitQuantile_eq_level {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    μ (unitQuantile μ a) = a := by
  have hq := unitQuantile_mem hμ h1 ha1
  have ha : a ∈ Set.Icc (μ 0) (μ (unitQuantile μ a)) := by
    exact ⟨by simpa only [h0] using ha0, hq.2⟩
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hq.1.1 hμ.continuousOn ha
  have hqx : unitQuantile μ a ≤ x := by
    apply csInf_le (unitQuantile_set_bddBelow μ a)
    exact ⟨⟨hx.1, hx.2.trans hq.1.2⟩, heq.ge⟩
  have hxq : x = unitQuantile μ a := le_antisymm hx.2 hqx
  simpa only [hxq] using heq

theorem unitQuantile_mem_Ioo {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    unitQuantile μ a ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq := (unitQuantile_mem hμ h1 ha1.le).1
  have heq := unitQuantile_eq_level hμ h0 h1 ha0.le ha1.le
  constructor
  · refine lt_of_le_of_ne hq.1 ?_
    intro he
    rw [← he, h0] at heq
    exact ha0.ne heq
  · refine lt_of_le_of_ne hq.2 ?_
    intro he
    rw [he, h1] at heq
    exact ha1.ne heq.symm

theorem unitQuantile_mono {μ : ℝ → ℝ} {a b : ℝ}
    (h1 : μ 1 = 1) (hab : a ≤ b) (hb : b ≤ 1) :
    unitQuantile μ a ≤ unitQuantile μ b := by
  apply csInf_le_csInf (unitQuantile_set_bddBelow μ a)
    (unitQuantile_set_nonempty h1 hb)
  intro p hp
  exact ⟨hp.1, hab.trans hp.2⟩

theorem unitQuantile_strictMonoOn {μ : ℝ → ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1) :
    StrictMonoOn (unitQuantile μ) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hle := unitQuantile_mono h1 hab.le hb.2
  refine lt_of_le_of_ne hle ?_
  intro heq
  have haeq := unitQuantile_eq_level hμ h0 h1 ha.1 ha.2
  have hbeq := unitQuantile_eq_level hμ h0 h1 hb.1 hb.2
  rw [heq, hbeq] at haeq
  exact hab.ne haeq.symm

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

lemma continuous_graphWeight {n : ℕ} (x : GraphConfig n) :
    Continuous (fun p : ℝ => graphWeight p x) := by
  classical
  unfold graphWeight
  apply continuous_finsetProd
  intro e he
  split_ifs <;> fun_prop

lemma continuous_graphMean {n : ℕ} (f : GraphConfig n → Bool) :
    Continuous (fun p : ℝ => graphMean p f) := by
  classical
  unfold graphMean
  apply continuous_finsetSum
  intro x hx
  exact (continuous_graphWeight x).mul continuous_const

lemma increasing_nontrivial_false {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    f (fun _ => false) = false := by
  obtain ⟨x, hx⟩ := hnt.2
  cases h : f (fun _ => false)
  · rfl
  · have hh := hmono (fun _ => false) x (by intro e he; cases he) h
    rw [hx] at hh
    contradiction

lemma increasing_nontrivial_true {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    f (fun _ => true) = true := by
  obtain ⟨x, hx⟩ := hnt.1
  exact hmono x (fun _ => true) (by intro e he; rfl) hx

lemma graphWeight_zero {n : ℕ} (x : GraphConfig n) :
    graphWeight 0 x = if x = (fun _ => false) then 1 else 0 := by
  classical
  by_cases hx : x = (fun _ => false)
  · subst x
    simp [graphWeight]
  · rw [ite_eq_right hx]
    obtain ⟨e, he⟩ : ∃ e, x e = true := by
      by_contra h
      apply hx
      funext e
      cases hxe : x e
      · rfl
      · exact False.elim (h ⟨e, hxe⟩)
    unfold graphWeight
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

lemma graphWeight_one {n : ℕ} (x : GraphConfig n) :
    graphWeight 1 x = if x = (fun _ => true) then 1 else 0 := by
  classical
  by_cases hx : x = (fun _ => true)
  · subst x
    simp [graphWeight]
  · rw [ite_eq_right hx]
    obtain ⟨e, he⟩ : ∃ e, x e = false := by
      by_contra h
      apply hx
      funext e
      cases hxe : x e
      · exact False.elim (h ⟨e, hxe⟩)
      · rfl
    unfold graphWeight
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

lemma graphMean_zero_eq {n : ℕ} (f : GraphConfig n → Bool) :
    graphMean 0 f = boolReal (f (fun _ => false)) := by
  classical
  simp [graphMean, graphWeight_zero]

lemma graphMean_one_eq {n : ℕ} (f : GraphConfig n → Bool) :
    graphMean 1 f = boolReal (f (fun _ => true)) := by
  classical
  simp [graphMean, graphWeight_one]

lemma graphMean_zero_of_increasing_nontrivial {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    graphMean 0 f = 0 := by
  rw [graphMean_zero_eq, increasing_nontrivial_false hmono hnt]
  rfl

lemma graphMean_one_of_increasing_nontrivial {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    graphMean 1 f = 1 := by
  rw [graphMean_one_eq, increasing_nontrivial_true hmono hnt]
  rfl

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

theorem graphQuantile_eq_unitQuantile {n : ℕ} (f : GraphConfig n → Bool) (a : ℝ) :
    graphQuantile a f = unitQuantile (fun p => graphMean p f) a := rfl

theorem graphMean_graphQuantile {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    graphMean (graphQuantile a f) f = a :=
  unitQuantile_eq_level (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt) ha0 ha1

theorem graphQuantile_mem_Ioo {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    graphQuantile a f ∈ Set.Ioo (0 : ℝ) 1 :=
  unitQuantile_mem_Ioo (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt) ha0 ha1

theorem graphQuantile_strictMonoOn {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    StrictMonoOn (fun a => graphQuantile a f) (Set.Icc (0 : ℝ) 1) :=
  unitQuantile_strictMonoOn (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt)

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- Derivative of the Bernoulli mass of a single graph configuration. -/
theorem hasDerivAt_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    HasDerivAt (fun q => graphWeight q x)
      (∑ e : GraphEdge n, (if x e = true then (1 : ℝ) else -1) *
        ∏ j ∈ Finset.univ.erase e, if x j = true then p else 1 - p) p := by
  classical
  have h (e : GraphEdge n) :
      HasDerivAt (fun q : ℝ => if x e = true then q else 1 - q)
        (if x e = true then (1 : ℝ) else -1) p := by
    split_ifs
    · exact hasDerivAt_id p
    · simpa using (hasDerivAt_id p).const_sub (1 : ℝ)
  simpa only [graphWeight, smul_eq_mul, mul_comm] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun e _ => h e))

/-- The finite product rule for the graph probability polynomial. -/
theorem hasDerivAt_graphMean_raw {n : ℕ} (f : GraphConfig n → Bool) (p : ℝ) :
    HasDerivAt (fun q => graphMean q f)
      (∑ e : GraphEdge n, ∑ x : GraphConfig n,
        ((if x e = true then (1 : ℝ) else -1) *
          ∏ j ∈ Finset.univ.erase e, if x j = true then p else 1 - p) *
          boolReal (f x)) p := by
  classical
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (GraphConfig n)))
    (fun x _ => (hasDerivAt_graphWeight p x).mul_const (boolReal (f x)))
  simp_rw [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  exact h

/-- The graph probability is a differentiable polynomial, without a monotonicity assumption. -/
theorem differentiable_graphMean {n : ℕ} (f : GraphConfig n → Bool) :
    Differentiable ℝ (fun p => graphMean p f) :=
  fun p => (hasDerivAt_graphMean_raw f p).differentiableAt

/-- Continuity of graph probability as a function of the edge bias. -/
theorem continuous_graphMean_russo {n : ℕ} (f : GraphConfig n → Bool) :
    Continuous (fun p => graphMean p f) :=
  (differentiable_graphMean f).continuous

/-- Every increasing property has nonnegative Boolean coordinate differences. -/
theorem increasing_update_false_true {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (x : GraphConfig n) (e : GraphEdge n) :
    f (Function.update x e false) = true → f (Function.update x e true) = true := by
  classical
  apply hf
  intro j hj
  by_cases hje : j = e
  · subst j
    simp
  · simpa [Function.update_of_ne hje] using hj

/-- For an increasing Boolean function the coordinate difference is its pivotal indicator. -/
theorem boolReal_update_sub_eq_indicator {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (x : GraphConfig n) (e : GraphEdge n) :
    boolReal (f (Function.update x e true)) - boolReal (f (Function.update x e false)) =
      if f (Function.update x e true) ≠ f (Function.update x e false) then 1 else 0 := by
  classical
  have h := increasing_update_false_true hf x e
  cases ht : f (Function.update x e true) <;>
    cases he : f (Function.update x e false) <;>
    simp_all [boolReal]

/-- Monotone pivotal influence is the expectation of the oriented coordinate difference. -/
theorem edgeInfluence_eq_sum_boolReal_sub {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) (e : GraphEdge n) :
    edgeInfluence p f e = ∑ x : GraphConfig n, graphWeight p x *
      (boolReal (f (Function.update x e true)) -
        boolReal (f (Function.update x e false))) := by
  classical
  unfold edgeInfluence
  apply Finset.sum_congr rfl
  intro x _
  rw [boolReal_update_sub_eq_indicator hf]
  split_ifs <;> simp

/-- Russo--Margulis formula with pivotal total influence.
The identity is polynomial, so no restriction to biases in `[0,1]` is necessary. -/
theorem hasDerivAt_graphMean {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) :
    HasDerivAt (fun q => graphMean q f) (totalInfluence p f) p := by
  classical
  convert hasDerivAt_graphMean_raw f p using 1
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro e _
  rw [edgeInfluence_eq_sum_boolReal_sub hf]
  exact (russo_sum_reindex p e (fun x => boolReal (f x))).symm

/-- Derivative form of the Russo--Margulis identity. -/
theorem deriv_graphMean {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) :
    deriv (fun q => graphMean q f) p = totalInfluence p f :=
  (hasDerivAt_graphMean hf p).deriv

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- The derivative of log odds, stated without any probability-specific definitions. -/
theorem hasDerivAt_log_odds {μ : ℝ → ℝ} {d x : ℝ}
    (hd : HasDerivAt μ d x) (hpos : 0 < μ x) (hone : μ x < 1) :
    HasDerivAt (fun t => Real.log (μ t) - Real.log (1 - μ t))
      (d / (μ x * (1 - μ x))) x := by
  have hne : μ x ≠ 0 := ne_of_gt hpos
  have hne' : 1 - μ x ≠ 0 := ne_of_gt (sub_pos.mpr hone)
  convert! (hd.log hne).sub (((hasDerivAt_const x (1 : ℝ)).sub hd).log hne') using 1
  dsimp only [Pi.sub_apply]
  field_simp
  ring

/-- Integrating a logistic differential inequality by the mean value theorem.
Continuity is needed on the closed interval, differentiability only in its interior. -/
theorem logistic_coordinate_width {μ μ' : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn μ (Set.Icc a b))
    (hμ : ∀ x ∈ Set.Icc a b, 0 < μ x ∧ μ x < 1)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt μ (μ' x) x)
    (hbound : ∀ x ∈ Set.Ioo a b, μ x * (1 - μ x) ≤ C * μ' x) :
    b - a ≤ C * ((Real.log (μ b) - Real.log (1 - μ b)) -
      (Real.log (μ a) - Real.log (1 - μ a))) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp
  let g : ℝ → ℝ := fun x => C * (Real.log (μ x) - Real.log (1 - μ x))
  let g' : ℝ → ℝ := fun x => C * (μ' x / (μ x * (1 - μ x)))
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.const_mul
    exact (hcont.log (fun x hx => ne_of_gt (hμ x hx).1)).sub
      ((continuousOn_const.sub hcont).log
        (fun x hx => ne_of_gt (sub_pos.mpr (hμ x hx).2)))
  have hgd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x := by
    intro x hx
    have hμx := hμ x (Set.Ioo_subset_Icc_self hx)
    exact (hasDerivAt_log_odds (hd x hx) hμx.1 hμx.2).const_mul C
  obtain ⟨x, hx, hslope⟩ := exists_hasDerivAt_eq_slope g g' hlt hg hgd
  have hμx := hμ x (Set.Ioo_subset_Icc_self hx)
  have hden : 0 < μ x * (1 - μ x) := mul_pos hμx.1 (sub_pos.mpr hμx.2)
  have hg' : 1 ≤ g' x := by
    dsimp [g']
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hden).2 (by simpa using hbound x hx)
  rw [hslope] at hg'
  have hle := (le_div_iff₀ (sub_pos.mpr hlt)).1 hg'
  dsimp [g] at hle
  linarith

/-- The symmetric endpoint form used in sharp-threshold estimates. -/
theorem logistic_width_of_hasDerivAt {μ μ' : ℝ → ℝ} {a b C ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (hεone : ε < 1)
    (hcont : ContinuousOn μ (Set.Icc a b))
    (hμ : ∀ x ∈ Set.Icc a b, 0 < μ x ∧ μ x < 1)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt μ (μ' x) x)
    (hbound : ∀ x ∈ Set.Ioo a b, μ x * (1 - μ x) ≤ C * μ' x)
    (ha : μ a = ε) (hb : μ b = 1 - ε) :
    b - a ≤ 2 * C * Real.log ((1 - ε) / ε) := by
  have h := logistic_coordinate_width hab hcont hμ hd hbound
  rw [ha, hb] at h
  have hsub : 1 - (1 - ε) = ε := by ring
  rw [hsub] at h
  rw [Real.log_div (ne_of_gt (sub_pos.mpr hεone)) (ne_of_gt hε)]
  linarith

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

/-- The logarithmic simplification used in the threshold-width estimate. -/
theorem log_odds_le_two_log_half_inv (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < (1 / 2 : ℝ)) :
    Real.log ((1 - ε) / ε) ≤ 2 * Real.log (1 / (2 * ε)) := by
  have hnum : 0 < 1 - ε := by linarith
  have hden : 0 < 2 * ε := by positivity
  have hratio : (1 - ε) / ε ≤ (1 / (2 * ε)) ^ 2 := by
    rw [div_pow, one_pow]
    apply (div_le_div_iff₀ hε (sq_pos_of_pos hden)).2
    nlinarith [mul_nonneg (le_of_lt hε) (sq_nonneg (1 - 2 * ε))]
  have hlog := Real.log_le_log (div_pos hnum hε) hratio
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- Multiplying the logarithmic estimate by a nonnegative constant. -/
theorem threshold_log_conversion (C ε w : ℝ) (hC : 0 ≤ C)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hw : w ≤ (2 * C) * Real.log ((1 - ε) / ε)) :
    w ≤ (4 * C) * Real.log (1 / (2 * ε)) := by
  calc
    w ≤ (2 * C) * Real.log ((1 - ε) / ε) := hw
    _ ≤ (2 * C) * (2 * Real.log (1 / (2 * ε))) :=
      mul_le_mul_of_nonneg_left (log_odds_le_two_log_half_inv ε hε hεhalf)
        (by positivity)
    _ = (4 * C) * Real.log (1 / (2 * ε)) := by ring

/-- The numerical constants relating the variance and threshold-width bounds. -/
theorem threshold_constant_conversion (t ε w : ℝ)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hw : w ≤ ((2 * (2 : ℝ) ^ 17) / t ^ 2) *
      Real.log ((1 - ε) / ε)) :
    w ≤ ((2 : ℝ) ^ 19 / t ^ 2) * Real.log (1 / (2 * ε)) := by
  have hC : 0 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by positivity
  have hw' : w ≤ (2 * ((2 : ℝ) ^ 17 / t ^ 2)) *
      Real.log ((1 - ε) / ε) := by
    convert hw using 1; ring
  have h := threshold_log_conversion ((2 : ℝ) ^ 17 / t ^ 2) ε w hC hε hεhalf hw'
  convert h using 1; ring

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem313

/-- The entire threshold-width deduction, with the variance estimate as its only
additional quantitative hypothesis. -/
theorem graphQuantile_width_of_variance_bound {n : ℕ} {f : GraphConfig n → Bool}
    {C ε : ℝ} (hC : 0 ≤ C)
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hvariance : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      graphVariance p f ≤ C * totalInfluence p f) :
    graphQuantile (1 - ε) f - graphQuantile ε f ≤
      (4 * C) * Real.log (1 / (2 * ε)) := by
  have hεone : ε < 1 := by linarith
  have hother0 : 0 < 1 - ε := by linarith
  have hother1 : 1 - ε < 1 := by linarith
  have ha := graphQuantile_mem_Ioo hmono hnt hε hεone
  have hb := graphQuantile_mem_Ioo hmono hnt hother0 hother1
  have hab : graphQuantile ε f ≤ graphQuantile (1 - ε) f := by
    exact (graphQuantile_strictMonoOn hmono hnt
      ⟨hε.le, hεone.le⟩ ⟨hother0.le, hother1.le⟩ (by linarith)).le
  have hrange : ∀ p ∈ Set.Icc (graphQuantile ε f) (graphQuantile (1 - ε) f),
      p ∈ Set.Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨ha.1.trans_le hp.1, hp.2.trans_lt hb.2⟩
  have hlog : graphQuantile (1 - ε) f - graphQuantile ε f ≤
      2 * C * Real.log ((1 - ε) / ε) := by
    apply logistic_width_of_hasDerivAt
      (μ := fun p => graphMean p f) (μ' := fun p => totalInfluence p f)
      hab hε hεone (continuous_graphMean f).continuousOn
    · intro p hp
      exact graphMean_mem_Ioo (hrange p hp).1 (hrange p hp).2 hnt
    · intro p hp
      exact hasDerivAt_graphMean hmono p
    · intro p hp
      have hv := hvariance p (hrange p (Set.Ioo_subset_Icc_self hp))
      simpa only [graphVariance_eq_mean_mul] using hv
    · exact graphMean_graphQuantile hmono hnt hε.le hεone.le
    · exact graphMean_graphQuantile hmono hnt hother0.le hother1.le
  exact threshold_log_conversion C ε
    (graphQuantile (1 - ε) f - graphQuantile ε f) hC hε hεhalf hlog

/-- The logarithmic-square threshold-width bound follows from the variance bound. -/
theorem sharp_threshold_width_of_variance_bound
    (hvariance : ∀ (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ),
      2 ≤ n → VertexInvariant f → 0 < p → p < 1 →
      graphVariance p f ≤ ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) *
        totalInfluence p f) :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) *
          Real.log (1 / (2 * ε)) := by
  intro n f ε hn hinvariant hmono hnt hε hεhalf
  have h := graphQuantile_width_of_variance_bound
    (C := (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2)
    (by positivity) hmono hnt hε hεhalf
    (fun p hp => hvariance n f p hn hinvariant hp.1 hp.2)
  convert h using 1; ring

end Problem313

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem313

theorem variance_influence_bound :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ), 2 ≤ n → VertexInvariant f → 0 < p → p < 1 → graphVariance p f ≤ ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact variance_influence_bound_core

theorem sharp_threshold_width_oai :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ), 2 ≤ n → VertexInvariant f → IncreasingGraphProperty f → NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) → graphQuantile (1 - ε) f - graphQuantile ε f ≤ ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε)) := by
  exact sharp_threshold_width_of_variance_bound variance_influence_bound

end Problem313

end

end OAI
end
end

theorem solution : type_of% @OAI.Problem313.sharp_threshold_width_oai := @OAI.Problem313.sharp_threshold_width_oai
