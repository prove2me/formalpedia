-- Prove2me | solution 1 for NumberField.exists_isBigO_card_absNorm_le_mk_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/50daa66f-c1d7-5a60-9b4b-efe0cfc48577

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.ClassNumber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub

set_option autoImplicit false

noncomputable section
section PART_R2

open MeasureTheory Module Bornology Filter Asymptotics Set Metric Submodule ZSpan Topology
open scoped Pointwise NNReal ENNReal

namespace ZLattice
p2m_export "ZLattice" "isAddFundamentalDomain covolume_eq_measure_fundamentalDomain rank covolume coe_comap"
namespace covolume
p2m_open "ZLattice.covolume ZLattice"

section NoMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} (b : Basis ι ℝ E)

private theorem lbR2_convex : Convex ℝ (fundamentalDomain b) := by
  have : fundamentalDomain b = ⋂ i, b.coord i ⁻¹' Set.Ico 0 1 := by
    ext x
    simp only [mem_fundamentalDomain, Set.mem_iInter, Set.mem_preimage, Basis.coord_apply]
  rw [this]
  exact convex_iInter fun i ↦ (convex_Ico 0 1).linear_preimage (b.coord i)

private theorem lbR2_subset_of_not_meet_frontier {T : Set E} {ℓ x : E}
    (hx₁ : x ∈ ℓ +ᵥ fundamentalDomain b) (hx₂ : x ∈ T)
    (h : ¬ ((ℓ +ᵥ fundamentalDomain b) ∩ frontier T).Nonempty) :
    ℓ +ᵥ fundamentalDomain b ⊆ T := by
  have hsub : ℓ +ᵥ fundamentalDomain b ⊆ interior T ∪ (closure T)ᶜ := by
    intro y hy
    by_contra hy'
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hy'
    exact h ⟨y, hy, hy'.2, hy'.1⟩
  rcases ((lbR2_convex b).vadd ℓ).isPreconnected.subset_or_subset isOpen_interior
      isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left interior_subset_closure) hsub
    with h' | h'
  · exact h'.trans interior_subset
  · exact absurd (subset_closure hx₂) (h' hx₁)

section Translates

variable [MeasurableSpace E] [BorelSpace E]

private theorem lbR2_measure_vadd (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ℓ : E) :
    μ (ℓ +ᵥ fundamentalDomain b) = μ (fundamentalDomain b) := by
  have : ℓ +ᵥ fundamentalDomain b = (fun x ↦ -ℓ + x) ⁻¹' fundamentalDomain b := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [this, measure_preimage_add]

private theorem lbR2_sum_measureReal_vadd (μ : Measure E) [Measure.IsAddHaarMeasure μ] (F : Finset E) :
    ∑ ℓ ∈ F, μ.real (ℓ +ᵥ fundamentalDomain b) = F.card * μ.real (fundamentalDomain b) := by
  simp_rw [measureReal_def, lbR2_measure_vadd b μ, Finset.sum_const, nsmul_eq_mul]

end Translates

variable [Fintype ι]

private theorem lbR2_mem_vadd_iff {ℓ x : E} (hℓ : ℓ ∈ span ℤ (Set.range b)) :
    x ∈ ℓ +ᵥ fundamentalDomain b ↔ (floor b x : E) = ℓ := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    show (floor b (ℓ + p) : E) = ℓ
    have h1 : fract b (ℓ + p) = p := by rw [fract_zSpan_add b p hℓ, fract_eq_self.mpr hp]
    have h2 : (floor b (ℓ + p) : E) = ℓ + p - fract b (ℓ + p) := by
      rw [fract_apply, sub_sub_cancel]
    rw [h2, h1, add_sub_cancel_right]
  · intro h
    refine ⟨fract b x, fract_mem_fundamentalDomain b x, ?_⟩
    show ℓ + fract b x = x
    rw [← h, fract_apply, add_sub_cancel]

private theorem lbR2_mem_floor_vadd (x : E) : x ∈ (floor b x : E) +ᵥ fundamentalDomain b :=
  (lbR2_mem_vadd_iff b (floor b x).2).mpr rfl

private theorem lbR2_self_mem_vadd {ℓ : E} (hℓ : ℓ ∈ span ℤ (Set.range b)) :
    ℓ ∈ ℓ +ᵥ fundamentalDomain b := by
  have := lbR2_mem_floor_vadd b ℓ
  rwa [floor_eq_self_of_mem b ℓ hℓ] at this

private theorem lbR2_disjoint {ℓ₁ ℓ₂ : E} (h₁ : ℓ₁ ∈ span ℤ (Set.range b))
    (h₂ : ℓ₂ ∈ span ℤ (Set.range b)) (h : ℓ₁ ≠ ℓ₂) :
    Disjoint (ℓ₁ +ᵥ fundamentalDomain b) (ℓ₂ +ᵥ fundamentalDomain b) :=
  Set.disjoint_left.mpr fun _ hx₁ hx₂ ↦
    h (((lbR2_mem_vadd_iff b h₁).mp hx₁).symm.trans ((lbR2_mem_vadd_iff b h₂).mp hx₂))

private theorem lbR2_exists_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ fundamentalDomain b, ‖p‖ ≤ D := by
  obtain ⟨D, hD, h⟩ := (fundamentalDomain_isBounded b).exists_pos_norm_le
  exact ⟨D, hD.le, h⟩

end NoMeasure

section Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem lbR2_cover_lipschitz {d : ℕ} {C : ℝ≥0} {g : (Fin d → ℝ) → E}
    (hg : LipschitzOnWith C g (Set.univ.pi fun _ ↦ Set.Icc 0 1)) {t : ℝ} (ht : 1 ≤ t) :
    ∃ s : Finset E, (s.card : ℝ) ≤ ((C : ℝ) + 3) ^ d * t ^ d ∧
      t • (g '' (Set.univ.pi fun _ ↦ Set.Icc 0 1)) ⊆ ⋃ x ∈ s, closedBall x 1 := by
  classical
  have hC : (0 : ℝ) ≤ C := C.coe_nonneg
  obtain ⟨N, hN₁, hNC, hN₂⟩ :
      ∃ N : ℕ, (1 : ℝ) ≤ N ∧ t * C ≤ N ∧ (N : ℝ) + 1 ≤ ((C : ℝ) + 3) * t := by
    refine ⟨⌈t * C⌉₊ + 1, ?_, ?_, ?_⟩
    · push_cast
      linarith [Nat.cast_nonneg (α := ℝ) ⌈t * C⌉₊]
    · push_cast
      linarith [Nat.le_ceil (t * C)]
    · push_cast
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ t * C)
      have h2 : t * C + 3 ≤ t * C + 3 * t := by linarith
      have h3 : t * C + 3 * t = ((C : ℝ) + 3) * t := by ring
      linarith
  have hN₀ : (0 : ℝ) < N := by linarith
  let pt : (Fin d → Fin (N + 1)) → (Fin d → ℝ) := fun k i ↦ ((k i : ℕ) : ℝ) / N
  have hpt : ∀ k, pt k ∈ Set.univ.pi fun (_ : Fin d) ↦ Set.Icc (0 : ℝ) 1 := by
    intro k
    rw [Set.mem_univ_pi]
    intro i
    have : ((k i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_add_one_iff.mp (k i).isLt
    exact ⟨div_nonneg (Nat.cast_nonneg _) hN₀.le, div_le_one_of_le₀ this hN₀.le⟩
  refine ⟨Finset.univ.image fun k ↦ t • g (pt k), ?_, ?_⟩
  · calc ((Finset.univ.image fun k ↦ t • g (pt k)).card : ℝ)
          ≤ (Finset.univ : Finset (Fin d → Fin (N + 1))).card := by
          exact_mod_cast Finset.card_image_le
      _ = ((N : ℝ) + 1) ^ d := by
          simp
      _ ≤ (((C : ℝ) + 3) * t) ^ d := pow_le_pow_left₀ (by positivity) hN₂ d
      _ = ((C : ℝ) + 3) ^ d * t ^ d := mul_pow _ _ _
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    have hq' := Set.mem_univ_pi.mp hq
    have hq0 : ∀ i, 0 ≤ q i := fun i ↦ (hq' i).1
    have hq1 : ∀ i, q i ≤ 1 := fun i ↦ (hq' i).2
    have hk : ∀ i, ⌊q i * N⌋₊ < N + 1 := fun i ↦ by
      rw [Nat.floor_lt (mul_nonneg (hq0 i) hN₀.le)]
      push_cast
      nlinarith [hq1 i, hN₀]
    let k : Fin d → Fin (N + 1) := fun i ↦ ⟨⌊q i * N⌋₊, hk i⟩
    have hdist : dist q (pt k) ≤ (N : ℝ)⁻¹ := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      change dist (q i) (((⌊q i * N⌋₊ : ℕ) : ℝ) / N) ≤ _
      have e1 : (⌊q i * N⌋₊ : ℝ) ≤ q i * N := Nat.floor_le (mul_nonneg (hq0 i) hN₀.le)
      have e2 : q i * N < ⌊q i * N⌋₊ + 1 := Nat.lt_floor_add_one _
      have e3 : (⌊q i * N⌋₊ : ℝ) / N ≤ q i := by rw [div_le_iff₀ hN₀]; exact e1
      have e4 : q i - (N : ℝ)⁻¹ ≤ (⌊q i * N⌋₊ : ℝ) / N := by
        rw [le_div_iff₀ hN₀, sub_mul, inv_mul_cancel₀ hN₀.ne']
        linarith
      have e5 : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hN₀
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith
    refine Set.mem_iUnion₂.mpr ⟨t • g (pt k), Finset.mem_image_of_mem _ (Finset.mem_univ k), ?_⟩
    rw [mem_closedBall, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith), ← dist_eq_norm]
    calc t * dist (g q) (g (pt k)) ≤ t * (C * dist q (pt k)) :=
          mul_le_mul_of_nonneg_left (hg.dist_le_mul q hq (pt k) (hpt k)) (by linarith)
      _ ≤ t * (C * (N : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist hC) (by linarith)
      _ = (t * C) / N := by ring
      _ ≤ 1 := div_le_one_of_le₀ hNC hN₀.le

end Cover

section WithMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℝ E)

private theorem lbR2_measure_vadd_ne_top (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ℓ : E) :
    μ (ℓ +ᵥ fundamentalDomain b) ≠ ∞ := by
  rw [lbR2_measure_vadd b μ]
  exact (fundamentalDomain_isBounded b).measure_lt_top.ne

private theorem lbR2_measureReal_pos (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    0 < μ.real (fundamentalDomain b) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_fundamentalDomain_ne_zero _)
    (fundamentalDomain_isBounded b).measure_lt_top.ne

private theorem lbR2_measureReal_biUnion (μ : Measure E) [Measure.IsAddHaarMeasure μ] (F : Finset E)
    (hF : ∀ ℓ ∈ F, ℓ ∈ span ℤ (Set.range b)) :
    μ.real (⋃ ℓ ∈ F, (ℓ +ᵥ fundamentalDomain b)) = F.card * μ.real (fundamentalDomain b) := by
  rw [measureReal_biUnion_finset
    (by intro ℓ₁ h₁ ℓ₂ h₂ hne; exact lbR2_disjoint b (hF ℓ₁ h₁) (hF ℓ₂ h₂) hne)
    (fun ℓ _ ↦ (fundamentalDomain_measurableSet b).const_vadd ℓ)
    (fun ℓ _ ↦ lbR2_measure_vadd_ne_top b μ ℓ)]
  simp_rw [measureReal_def, lbR2_measure_vadd b μ, Finset.sum_const, nsmul_eq_mul]

private theorem lbR2_card_mul_le (μ : Measure E) [Measure.IsAddHaarMeasure μ] {D : ℝ}
    (hD : ∀ p ∈ fundamentalDomain b, ‖p‖ ≤ D) (x : E) (F : Finset E)
    (hF₁ : ∀ ℓ ∈ F, ℓ ∈ span ℤ (Set.range b)) (hF₂ : ∀ ℓ ∈ F, ‖ℓ - x‖ ≤ 1 + D) :
    F.card * μ.real (fundamentalDomain b) ≤ μ.real (closedBall (0 : E) (1 + 2 * D)) := by
  rw [← lbR2_measureReal_biUnion b μ F hF₁, ← Measure.addHaar_real_closedBall_center μ x]
  refine measureReal_mono ?_ measure_closedBall_lt_top.ne
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨ℓ, hℓ, p, hp, rfl⟩ := hy
  show ℓ + p ∈ closedBall x (1 + 2 * D)
  rw [mem_closedBall, dist_eq_norm, add_sub_right_comm]
  calc ‖ℓ - x + p‖ ≤ ‖ℓ - x‖ + ‖p‖ := norm_add_le _ _
    _ ≤ (1 + D) + D := add_le_add (hF₂ ℓ hℓ) (hD p hp)
    _ = 1 + 2 * D := by ring

private theorem lbR2_core (μ : Measure E) [Measure.IsAddHaarMeasure μ] {T : Set E} (hT₁ : IsBounded T)
    (B : Finset E)
    (hB : ∀ ℓ ∈ span ℤ (Set.range b), ((ℓ +ᵥ fundamentalDomain b) ∩ frontier T).Nonempty →
      ℓ ∈ B) :
    |(Nat.card (T ∩ span ℤ (Set.range b) : Set E) : ℝ) -
      μ.real T / μ.real (fundamentalDomain b)| ≤ B.card := by
  classical
  have hPpos := lbR2_measureReal_pos b μ
  have hfin : (T ∩ span ℤ (Set.range b)).Finite := setFinite_inter b hT₁
  obtain ⟨A, hA⟩ : ∃ A : Finset E, ∀ ℓ, ℓ ∈ A ↔ ℓ ∈ T ∧ ℓ ∈ span ℤ (Set.range b) :=
    ⟨hfin.toFinset, fun ℓ ↦ by simp⟩
  have hcard : Nat.card (T ∩ span ℤ (Set.range b) : Set E) = A.card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext ℓ
    simp [hA]
  obtain ⟨I, hI⟩ : ∃ I : Finset E, ∀ ℓ, ℓ ∈ I ↔ ℓ ∈ A ∧ ℓ +ᵥ fundamentalDomain b ⊆ T :=
    ⟨A.filter fun ℓ ↦ ℓ +ᵥ fundamentalDomain b ⊆ T, fun ℓ ↦ by simp⟩

  have h_i : A ⊆ I ∪ B := by
    intro ℓ hℓ
    rw [Finset.mem_union]
    by_cases hℓB : ℓ ∈ B
    · exact Or.inr hℓB
    · obtain ⟨hℓT, hℓΛ⟩ := (hA ℓ).mp hℓ
      exact Or.inl <| (hI ℓ).mpr ⟨hℓ, lbR2_subset_of_not_meet_frontier b
        (lbR2_self_mem_vadd b hℓΛ) hℓT (fun h ↦ hℓB (hB ℓ hℓΛ h))⟩

  have h_ii : (I.card : ℝ) * μ.real (fundamentalDomain b) ≤ μ.real T := by
    have hIΛ : ∀ ℓ ∈ I, ℓ ∈ span ℤ (Set.range b) := fun ℓ hℓ ↦ ((hA ℓ).mp ((hI ℓ).mp hℓ).1).2
    rw [← lbR2_measureReal_biUnion b μ I hIΛ]
    refine measureReal_mono ?_ hT₁.measure_lt_top.ne
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨ℓ, hℓ, hy⟩ := hy
    exact ((hI ℓ).mp hℓ).2 hy

  have h_iii : μ.real T ≤ ((I.card : ℝ) + B.card) * μ.real (fundamentalDomain b) := by
    have hcov : T ⊆ ⋃ ℓ ∈ I ∪ B, (ℓ +ᵥ fundamentalDomain b) := by
      intro x hx
      simp only [Set.mem_iUnion]
      have hℓΛ : (floor b x : E) ∈ span ℤ (Set.range b) := (floor b x).2
      have hxℓ : x ∈ (floor b x : E) +ᵥ fundamentalDomain b := lbR2_mem_floor_vadd b x
      by_cases hℓB : (floor b x : E) ∈ B
      · exact ⟨floor b x, Finset.mem_union_right _ hℓB, hxℓ⟩
      · have hsub := lbR2_subset_of_not_meet_frontier b hxℓ hx (fun h ↦ hℓB (hB _ hℓΛ h))
        exact ⟨floor b x, Finset.mem_union_left _ <| (hI _).mpr
          ⟨(hA _).mpr ⟨hsub (lbR2_self_mem_vadd b hℓΛ), hℓΛ⟩, hsub⟩, hxℓ⟩
    have hne : μ (⋃ ℓ ∈ I ∪ B, (ℓ +ᵥ fundamentalDomain b)) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun ℓ _ ↦ lbR2_measure_vadd_ne_top b μ ℓ)
        (measure_biUnion_finset_le _ _)
    calc μ.real T ≤ μ.real (⋃ ℓ ∈ I ∪ B, (ℓ +ᵥ fundamentalDomain b)) := measureReal_mono hcov hne
      _ ≤ ∑ ℓ ∈ I ∪ B, μ.real (ℓ +ᵥ fundamentalDomain b) := measureReal_biUnion_finset_le _ _
      _ = ((I ∪ B).card : ℝ) * μ.real (fundamentalDomain b) := lbR2_sum_measureReal_vadd b μ _
      _ ≤ ((I.card : ℝ) + B.card) * μ.real (fundamentalDomain b) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_union_le I B)
            measureReal_nonneg

  have hN : (A.card : ℝ) ≤ I.card + B.card := by
    exact_mod_cast (Finset.card_le_card h_i).trans (Finset.card_union_le I B)
  have hIA : (I.card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card (fun ℓ hℓ ↦ ((hI ℓ).mp hℓ).1)
  have h2 : (I.card : ℝ) ≤ μ.real T / μ.real (fundamentalDomain b) := by
    rw [le_div_iff₀ hPpos]; exact h_ii
  have h3 : μ.real T / μ.real (fundamentalDomain b) ≤ I.card + B.card := by
    rw [div_le_iff₀ hPpos]; exact h_iii
  rw [hcard, abs_sub_le_iff]
  constructor <;> linarith

private theorem lbR2_core_cover (μ : Measure E) [Measure.IsAddHaarMeasure μ] {D : ℝ}
    (hD : ∀ p ∈ fundamentalDomain b, ‖p‖ ≤ D) {T : Set E} (hT₁ : IsBounded T)
    (s : Finset E) (hs : frontier T ⊆ ⋃ x ∈ s, closedBall x 1) :
    |(Nat.card (T ∩ span ℤ (Set.range b) : Set E) : ℝ) - μ.real T / μ.real (fundamentalDomain b)|
      ≤ s.card * (μ.real (closedBall (0 : E) (1 + 2 * D)) / μ.real (fundamentalDomain b)) := by
  classical
  have hPpos := lbR2_measureReal_pos b μ
  obtain ⟨Bx, hBx⟩ : ∃ Bx : E → Finset E, ∀ x ℓ, ℓ ∈ Bx x ↔
      ‖ℓ - x‖ ≤ 1 + D ∧ ℓ ∈ span ℤ (Set.range b) :=
    ⟨fun x ↦ (setFinite_inter b (isBounded_closedBall (x := x) (r := 1 + D))).toFinset,
      fun x ℓ ↦ by simp [dist_eq_norm]⟩
  have hBx_card : ∀ x, ((Bx x).card : ℝ) ≤
      μ.real (closedBall (0 : E) (1 + 2 * D)) / μ.real (fundamentalDomain b) := by
    intro x
    rw [le_div_iff₀ hPpos]
    exact lbR2_card_mul_le b μ hD x (Bx x) (fun ℓ hℓ ↦ ((hBx x ℓ).mp hℓ).2)
      (fun ℓ hℓ ↦ ((hBx x ℓ).mp hℓ).1)
  refine (lbR2_core b μ hT₁ (s.biUnion Bx) ?_).trans ?_
  · rintro ℓ hℓ ⟨_, ⟨p, hp, rfl⟩, hy⟩
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hs hy)
    rw [Finset.mem_biUnion]
    refine ⟨x, hx, (hBx x ℓ).mpr ⟨?_, hℓ⟩⟩
    replace hyx : ‖ℓ + p - x‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_eq_norm, vadd_eq_add] using hyx
    calc ‖ℓ - x‖ = ‖(ℓ + p - x) - p‖ := by congr 1; abel
      _ ≤ ‖ℓ + p - x‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ 1 + D := add_le_add hyx (hD p hp)
  · calc ((s.biUnion Bx).card : ℝ) ≤ ∑ x ∈ s, ((Bx x).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ x ∈ s, μ.real (closedBall (0 : E) (1 + 2 * D)) / μ.real (fundamentalDomain b) :=
          Finset.sum_le_sum fun x _ ↦ hBx_card x
      _ = s.card * (μ.real (closedBall (0 : E) (1 + 2 * D)) / μ.real (fundamentalDomain b)) := by
          rw [Finset.sum_const, nsmul_eq_mul]

end WithMeasure

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem isBigO_card_le_sub (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ finrank ℝ E * F x)
    (h₁ : IsBounded {x ∈ X | F x ≤ 1}) (h₂ : MeasurableSet {x ∈ X | F x ≤ 1})
    {d m : ℕ} (hd : d + 1 = finrank ℝ E) (C : NNReal) (f : Fin m → (Fin d → ℝ) → E)
    (hf : ∀ i, LipschitzOnWith C (f i) (Set.univ.pi fun _ ↦ Set.Icc 0 1))
    (h₃ : frontier {x ∈ X | F x ≤ 1} ⊆ ⋃ i, f i '' (Set.univ.pi fun _ ↦ Set.Icc 0 1)) :
    (fun c : ℝ ↦ (Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) : ℝ)
        - μ.real {x ∈ X | F x ≤ 1} / covolume L μ * c)
      =O[atTop] fun c ↦ c ^ (1 - (finrank ℝ E : ℝ)⁻¹) := by
  classical
  have _hmeas := h₂
  have hn₀ : finrank ℝ E ≠ 0 := by omega
  have hn₀' : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hn₀
  set S := {x ∈ X | F x ≤ 1} with hS

  obtain ⟨b, hΛ, hcov⟩ : ∃ b : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ E,
      span ℤ (Set.range b) = L ∧ covolume L μ = μ.real (fundamentalDomain b) :=
    ⟨(Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L,
      (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L,
      covolume_eq_measure_fundamentalDomain L μ
        (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ)⟩
  obtain ⟨D, hD₀, hD⟩ := lbR2_exists_bound b
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ,
      μ.real (closedBall (0 : E) (1 + 2 * D)) / μ.real (fundamentalDomain b) = M := ⟨_, rfl⟩
  have hM₀ : 0 ≤ M := hM_def ▸ div_nonneg measureReal_nonneg measureReal_nonneg

  have hscale : ∀ c : ℝ, 0 < c →
      {x ∈ X | F x ≤ c} = (c ^ (finrank ℝ E : ℝ)⁻¹) • S := by
    intro c hc
    have hc' : 0 < c ^ (finrank ℝ E : ℝ)⁻¹ := Real.rpow_pos_of_pos hc _
    have hcn : (c ^ (finrank ℝ E : ℝ)⁻¹) ^ finrank ℝ E = c :=
      Real.rpow_inv_natCast_pow hc.le hn₀
    ext x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      refine ⟨(c ^ (finrank ℝ E : ℝ)⁻¹)⁻¹ • x, ⟨hX hx₁ (inv_pos.mpr hc'), ?_⟩,
        smul_inv_smul₀ hc'.ne' x⟩
      rw [hF _ (inv_pos.mpr hc').le, inv_pow, hcn, inv_mul_le_iff₀ hc, mul_one]
      exact hx₂
    · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
      refine ⟨hX hy₁ hc', ?_⟩
      rw [hF _ hc'.le, hcn]
      exact mul_le_of_le_one_right hc.le hy₂

  have key : ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ((t • S) ∩ L : Set E) : ℝ) - μ.real S / covolume L μ * t ^ finrank ℝ E| ≤
        (m * ((C : ℝ) + 3) ^ d * M) * t ^ d := by
    intro t ht
    have ht₀ : 0 < t := one_pos.trans_le ht
    have hfr : frontier (t • S) = t • frontier S :=
      ((Homeomorph.smulOfNeZero t ht₀.ne').image_frontier S).symm
    choose s hs₁ hs₂ using fun i ↦ lbR2_cover_lipschitz (E := E) (hf i) ht
    have hcover : frontier (t • S) ⊆ ⋃ x ∈ Finset.univ.biUnion s, closedBall x 1 := by
      rw [hfr]
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h₃ hz)
      have := hs₂ i (Set.smul_mem_smul_set hi : t • z ∈ t • (f i '' _))
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨x, hx, hx'⟩ := this
      exact ⟨x, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩, hx'⟩
    have hbd : IsBounded (t • S) := h₁.smul₀ t
    have hμt : μ.real (t • S) = t ^ finrank ℝ E * μ.real S := by
      rw [measureReal_def, Measure.addHaar_smul_of_nonneg μ ht₀.le, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
    have := lbR2_core_cover b μ hD hbd (Finset.univ.biUnion s) hcover
    rw [hΛ, hμt, hM_def] at this
    rw [hcov]
    refine (le_of_eq ?_).trans (this.trans ?_)
    · congr 1
      ring
    · have hsum : ((Finset.univ.biUnion s).card : ℝ) ≤ ∑ i, ((s i).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      have hsum' : ∑ i, ((s i).card : ℝ) ≤ ∑ _i : Fin m, ((C : ℝ) + 3) ^ d * t ^ d :=
        Finset.sum_le_sum fun i _ ↦ hs₁ i
      calc ((Finset.univ.biUnion s).card : ℝ) * M
            ≤ (∑ _i : Fin m, ((C : ℝ) + 3) ^ d * t ^ d) * M :=
            mul_le_mul_of_nonneg_right (hsum.trans hsum') hM₀
        _ = (m * ((C : ℝ) + 3) ^ d * M) * t ^ d := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring

  have hbound : ∀ c : ℝ, 1 ≤ c →
      |(Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) : ℝ) - μ.real S / covolume L μ * c| ≤
        (m * ((C : ℝ) + 3) ^ d * M) * c ^ (1 - (finrank ℝ E : ℝ)⁻¹) := by
    intro c hc
    have hc₀ : 0 < c := one_pos.trans_le hc
    have hc' : 1 ≤ c ^ (finrank ℝ E : ℝ)⁻¹ := Real.one_le_rpow hc (by positivity)
    have hcn : (c ^ (finrank ℝ E : ℝ)⁻¹) ^ finrank ℝ E = c :=
      Real.rpow_inv_natCast_pow hc₀.le hn₀
    have hcd : (c ^ (finrank ℝ E : ℝ)⁻¹) ^ d = c ^ (1 - (finrank ℝ E : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc₀.le]
      congr 1
      have : (d : ℝ) = finrank ℝ E - 1 := by
        rw [← hd]
        push_cast
        ring
      rw [this, mul_sub, mul_one, inv_mul_cancel₀ hn₀']
    rw [hscale c hc₀, ← hcd]
    have := key _ hc'
    rw [hcn] at this
    exact this

  refine IsBigO.of_bound (m * ((C : ℝ) + 3) ^ d * M) ?_
  filter_upwards [eventually_ge_atTop 1] with c hc
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (one_pos.trans_le hc) _)]
  exact hbound c hc

end Main

end ZLattice.covolume

end PART_R2

section PART_R3

namespace NumberField
p2m_export "NumberField" "classNumber_pos Units.rank discr mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice place mixedEmbedding InfinitePlace dedekindZeta_residue_def classNumber mixedEmbedding.norm mixedEmbedding.norm_smul dedekindZeta_residue"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "mem_idealLattice euclidean.toMixed index normAtAllPlaces fundamentalCone idealLattice normAtPlace mixedSpace euclidean.mixedSpace euclidean.finrank normAtPlace_apply_of_isReal norm_smul realSpace normAtPlace_apply_of_isComplex"
namespace fundamentalCone
p2m_export "NumberField.mixedEmbedding.fundamentalCone" "closure_paramSet expMapBasis_apply'' idealSet subset_interior_normLeOne normLeOne measurableSet_normLeOne expMap_apply paramSet card_isPrincipal_dvd_norm_le mem_idealSet compactSet expMap equivFinRank closure_normLeOne_subset completeBasis isBounded_normLeOne compactSet_eq_union smul_mem_iff_mem expMapBasis interior_paramSet"
p2m_open "NumberField.mixedEmbedding.fundamentalCone NumberField.mixedEmbedding NumberField"

p2m_open "NumberField P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem MeasureTheory Set"

open scoped Real NNReal Classical

variable {K : Type*} [Field K] [NumberField K]

private abbrev aux4Box (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1

private theorem aux4_convex_box {ι : Type*} : Convex ℝ (aux4Box ι) :=
  convex_pi fun _ _ ↦ convex_Icc 0 1

private theorem aux4_isCompact_box {ι : Type*} [Fintype ι] : IsCompact (aux4Box ι) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

private theorem aux4_exists_lipschitzOnWith_of_contDiff {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : ContDiff ℝ 1 f) :
    ∃ C, LipschitzOnWith C f (aux4Box ι) :=
  (hf.contDiffOn (s := aux4Box ι)).exists_lipschitzOnWith one_ne_zero
    aux4_convex_box aux4_isCompact_box

private theorem aux4_contDiff_expMap :
    ContDiff ℝ 1 (expMap : realSpace K → realSpace K) := by
  have h : (expMap : realSpace K → realSpace K)
      = fun x w ↦ Real.exp ((w.mult : ℝ)⁻¹ * x w) := by
    ext x w
    exact expMap_apply x w
  rw [h]
  exact contDiff_pi.mpr fun w ↦
    Real.contDiff_exp.comp ((contDiff_const (c := (w.mult : ℝ)⁻¹)).mul (contDiff_apply ℝ ℝ w))

private theorem aux4_contDiff_expMapBasis :
    ContDiff ℝ 1 (expMapBasis : realSpace K → realSpace K) := by
  have h : (expMapBasis : realSpace K → realSpace K)
      = (expMap : realSpace K → realSpace K) ∘ (completeBasis K).equivFunL.symm := rfl
  rw [h]
  exact aux4_contDiff_expMap.comp ((completeBasis K).equivFunL.symm : _ ≃L[ℝ] _).contDiff

open scoped Classical in

private def aux4Embed (y : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  fun w ↦ if h : w = w₀ then 0 else y ⟨w, h⟩

open scoped Classical in
private theorem aux4_contDiff_embed :
    ContDiff ℝ 1 (aux4Embed (K := K)) := by
  refine contDiff_pi.mpr fun w ↦ ?_
  by_cases h : w = w₀
  · simpa [aux4Embed, h] using contDiff_const (c := (0 : ℝ))
  · simpa [aux4Embed, h] using contDiff_apply ℝ ℝ (⟨w, h⟩ : {w : InfinitePlace K // w ≠ w₀})

private def aux4Top : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K :=
  fun y ↦ expMapBasis (aux4Embed y)

private theorem aux4_contDiff_top : ContDiff ℝ 1 (aux4Top (K := K)) :=
  aux4_contDiff_expMapBasis.comp aux4_contDiff_embed

open scoped Classical in

private def aux4Face (w₁ : {w : InfinitePlace K // w ≠ w₀}) (b : Bool) :
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K :=
  fun y ↦ (y w₁) •
    expMapBasis (aux4Embed fun j ↦ if j = w₁ then (if b then 1 else 0) else y j)

open scoped Classical in
private theorem aux4_contDiff_face (w₁ : {w : InfinitePlace K // w ≠ w₀}) (b : Bool) :
    ContDiff ℝ 1 (aux4Face (K := K) w₁ b) := by
  refine (contDiff_apply ℝ ℝ w₁).smul (aux4_contDiff_expMapBasis.comp
    (aux4_contDiff_embed.comp (contDiff_pi.mpr fun j ↦ ?_)))
  by_cases h : j = w₁
  · simpa [h] using contDiff_const (c := if b then (1 : ℝ) else 0)
  · simpa [h] using contDiff_apply ℝ ℝ j

open scoped Classical in

private theorem aux4_cover_realSpace :
    compactSet K \ expMapBasis '' (interior (paramSet K)) ⊆
      (aux4Top '' aux4Box _) ∪
        (⋃ w₁ : {w : InfinitePlace K // w ≠ w₀}, ⋃ b : Bool,
          aux4Face w₁ b '' aux4Box _) ∪
        {(0 : realSpace K)} := by
  rintro x ⟨hx₁, hx₂⟩
  rw [compactSet_eq_union] at hx₁
  rcases hx₁ with hx₁ | hx₁
  · obtain ⟨y, hy, rfl⟩ := hx₁
    rw [closure_paramSet, mem_univ_pi] at hy
    by_cases h₀ : y w₀ = 0
    ·
      refine Or.inl (Or.inl ⟨fun j ↦ y j.1, ?_, ?_⟩)
      · exact mem_univ_pi.mpr fun j ↦ by simpa [if_neg j.2] using hy j.1
      · have h : aux4Embed (fun j : {w : InfinitePlace K // w ≠ w₀} ↦ y j.1) = y := by
          ext w
          by_cases h : w = w₀
          · rw [aux4Embed, dif_pos h, h, h₀]
          · rw [aux4Embed, dif_neg h]
        rw [aux4Top, h]
    · by_cases h₁ : ∃ w₁ : {w : InfinitePlace K // w ≠ w₀}, y w₁.1 = 0 ∨ y w₁.1 = 1
      ·
        obtain ⟨w₁, hb⟩ := h₁
        set bv : Bool := decide (y w₁.1 = 1) with hbv
        have hbval : (if bv then (1 : ℝ) else 0) = y w₁.1 := by
          rcases hb with hb | hb
          · have : bv = false := by simp [hbv, hb]
            rw [this, if_neg Bool.false_ne_true, hb]
          · have : bv = true := by simp [hbv, hb]
            rw [this, if_pos rfl, hb]
        refine Or.inl (Or.inr (mem_iUnion.mpr ⟨w₁, mem_iUnion.mpr ⟨bv,
          ⟨fun j ↦ if j = w₁ then Real.exp (y w₀) else y j.1, ?_, ?_⟩⟩⟩))
        · refine mem_univ_pi.mpr fun j ↦ ?_
          by_cases h : j = w₁
          · rw [if_pos h]
            exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by simpa using hy w₀)⟩
          · rw [if_neg h]
            simpa [if_neg j.2] using hy j.1
        ·
          have hinner : (fun j : {w : InfinitePlace K // w ≠ w₀} ↦
              if j = w₁ then (if bv then (1 : ℝ) else 0)
              else if j = w₁ then Real.exp (y w₀) else y j.1) =
                fun j ↦ y j.1 := by
            ext j
            by_cases h : j = w₁
            · rw [if_pos h, hbval, h]
            · rw [if_neg h, if_neg h]
          have hemb : aux4Embed (fun j : {w : InfinitePlace K // w ≠ w₀} ↦ y j.1) =
              fun w ↦ if w = w₀ then 0 else y w := by
            ext w
            by_cases h : w = w₀
            · rw [aux4Embed, dif_pos h, if_pos h]
            · rw [aux4Embed, dif_neg h, if_neg h]
          rw [aux4Face, if_pos rfl, hinner, hemb, ← expMapBasis_apply'']
      ·
        exfalso
        apply hx₂
        refine ⟨y, ?_, rfl⟩
        rw [interior_paramSet, mem_univ_pi]
        intro w
        by_cases h : w = w₀
        · rw [if_pos h]
          have h1 : y w ≤ 0 := by simpa [h] using hy w
          have h2 : y w ≠ 0 := by rw [h]; exact h₀
          exact Set.mem_Iio.mpr (lt_of_le_of_ne h1 h2)
        · rw [if_neg h]
          have hmem : y w ∈ Set.Icc (0 : ℝ) 1 := by simpa [if_neg h] using hy w
          have hne := not_exists.mp h₁ ⟨w, h⟩
          rw [not_or] at hne
          exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne.1), lt_of_le_of_ne hmem.2 hne.2⟩
  · exact Or.inr hx₁

private theorem aux4_frontier_normLeOne_subset :
    frontier (normLeOne K) ⊆
      normAtAllPlaces ⁻¹' (compactSet K \ expMapBasis '' (interior (paramSet K))) := by
  intro x hx
  rw [Set.mem_preimage, Set.mem_diff]
  exact ⟨closure_normLeOne_subset K hx.1, fun h ↦ hx.2 (subset_interior_normLeOne K h)⟩

private abbrev aux4J (K : Type*) [Field K] [NumberField K] : Type _ :=
  {w : InfinitePlace K // w ≠ w₀} ⊕ {w : InfinitePlace K // IsComplex w}

private def aux4Lift (g : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K)
    (ε : {w : InfinitePlace K // IsReal w} → Bool) :
    (aux4J K → ℝ) → mixedSpace K :=
  fun y ↦
    (fun w ↦ (if ε w then 1 else -1) * g (y ∘ Sum.inl) w.1,
     fun w ↦ (g (y ∘ Sum.inl) w.1 : ℂ) *
       Complex.exp (((2 * π * y (Sum.inr w) - π : ℝ) : ℂ) * Complex.I))

private theorem aux4_contDiff_lift {g : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K}
    (hg : ContDiff ℝ 1 g) (ε : {w : InfinitePlace K // IsReal w} → Bool) :
    ContDiff ℝ 1 (aux4Lift g ε) := by
  have hpre : ContDiff ℝ 1 (fun y : aux4J K → ℝ ↦ y ∘ Sum.inl) :=
    contDiff_pi.mpr fun j ↦ contDiff_apply ℝ ℝ (Sum.inl j)
  refine ContDiff.prodMk ?_ ?_
  · exact contDiff_pi.mpr fun w ↦
      contDiff_const.mul (((contDiff_pi.mp hg) w.1).comp hpre)
  · refine contDiff_pi.mpr fun w ↦ ContDiff.mul ?_ ?_
    · exact Complex.ofRealCLM.contDiff.comp (((contDiff_pi.mp hg) w.1).comp hpre)
    · have hexp : ContDiff ℝ 1 (Complex.exp : ℂ → ℂ) := Complex.contDiff_exp
      refine hexp.comp ?_
      exact (Complex.ofRealCLM.contDiff.comp
        ((contDiff_const.mul (contDiff_apply ℝ ℝ (Sum.inr w))).sub contDiff_const)).mul
        contDiff_const

private theorem aux4_lift_cover {g : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K}
    {x : mixedSpace K} (hx : normAtAllPlaces x ∈ g '' aux4Box _) :
    ∃ ε : {w : InfinitePlace K // IsReal w} → Bool,
      x ∈ aux4Lift g ε '' aux4Box (aux4J K) := by
  classical
  obtain ⟨u, hu, hgu⟩ := hx
  have hgu' : ∀ w, g u w = normAtPlace w x := fun w ↦ by rw [hgu]
  refine ⟨fun w ↦ decide (0 ≤ x.1 w),
    Sum.elim u (fun w ↦ Complex.arg (x.2 w) / (2 * π) + 1 / 2), ?_, ?_⟩
  · refine mem_univ_pi.mpr fun j ↦ ?_
    rcases j with j | w
    · exact mem_univ_pi.mp hu j
    · simp only [Sum.elim_inr]
      constructor
      · have h := Complex.neg_pi_lt_arg (x.2 w)
        have h2π : (0 : ℝ) < 2 * π := by positivity
        have h1 : (-(1 / 2) : ℝ) * (2 * π) ≤ Complex.arg (x.2 w) := by nlinarith
        have h2 : (-(1 / 2) : ℝ) ≤ Complex.arg (x.2 w) / (2 * π) := (le_div_iff₀ h2π).mpr h1
        linarith
      · have h := Complex.arg_le_pi (x.2 w)
        have h2π : (0 : ℝ) < 2 * π := by positivity
        have h1 : Complex.arg (x.2 w) ≤ (1 / 2 : ℝ) * (2 * π) := by nlinarith
        have h2 : Complex.arg (x.2 w) / (2 * π) ≤ (1 / 2 : ℝ) := (div_le_iff₀ h2π).mpr h1
        linarith
  · refine Prod.ext ?_ ?_
    · ext w
      have hg : g (Sum.elim u
          (fun w ↦ Complex.arg (x.2 w) / (2 * π) + 1 / 2) ∘ Sum.inl) w.1 = ‖x.1 w‖ := by
        rw [Sum.elim_comp_inl, hgu' w.1, normAtPlace_apply_of_isReal w.2]
      simp only [aux4Lift]
      rw [hg]
      by_cases hs : 0 ≤ x.1 w
      · simp [hs, Real.norm_eq_abs, abs_of_nonneg hs]
      · simp [hs, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hs)]
    · ext w
      have hg : g (Sum.elim u
          (fun w ↦ Complex.arg (x.2 w) / (2 * π) + 1 / 2) ∘ Sum.inl) w.1 = ‖x.2 w‖ := by
        rw [Sum.elim_comp_inl, hgu' w.1, normAtPlace_apply_of_isComplex w.2]
      have harg : 2 * π * (Complex.arg (x.2 w) / (2 * π) + 1 / 2) - π
          = Complex.arg (x.2 w) := by
        have hπ : (2 * π : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      simp only [aux4Lift, Sum.elim_inr]
      rw [hg, harg]
      exact Complex.norm_mul_exp_arg_mul_I (x.2 w)

private abbrev aux4PieceIdx (K : Type*) [Field K] [NumberField K] : Type _ :=
  Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool) ⊕ Unit

private def aux4Piece : aux4PieceIdx K → ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K
  | Sum.inl _ => aux4Top
  | Sum.inr (Sum.inl p) => aux4Face p.1 p.2
  | Sum.inr (Sum.inr _) => fun _ ↦ 0

private theorem aux4_contDiff_piece (p : aux4PieceIdx K) : ContDiff ℝ 1 (aux4Piece p) := by
  rcases p with _ | p | _
  · exact aux4_contDiff_top
  · exact aux4_contDiff_face p.1 p.2
  · exact contDiff_const

private abbrev aux4CoverIdx (K : Type*) [Field K] [NumberField K] : Type _ :=
  aux4PieceIdx K × ({w : InfinitePlace K // IsReal w} → Bool)

private def aux4CoverMap (p : aux4CoverIdx K) : (aux4J K → ℝ) → mixedSpace K :=
  aux4Lift (aux4Piece p.1) p.2

private theorem aux4_contDiff_coverMap (p : aux4CoverIdx K) :
    ContDiff ℝ 1 (aux4CoverMap p) :=
  aux4_contDiff_lift (aux4_contDiff_piece p.1) p.2

private theorem aux4_cover_mixed :
    frontier (normLeOne K) ⊆
      ⋃ p : aux4CoverIdx K, aux4CoverMap p '' aux4Box (aux4J K) := by
  intro x hx
  have h₂ := aux4_cover_realSpace (aux4_frontier_normLeOne_subset hx)
  rcases h₂ with (h | h) | h
  · obtain ⟨ε, hε⟩ := aux4_lift_cover h
    exact mem_iUnion.mpr ⟨(Sum.inl (), ε), hε⟩
  · rw [mem_iUnion] at h
    obtain ⟨w₁, h⟩ := h
    rw [mem_iUnion] at h
    obtain ⟨b, h⟩ := h
    obtain ⟨ε, hε⟩ := aux4_lift_cover h
    exact mem_iUnion.mpr ⟨(Sum.inr (Sum.inl (w₁, b)), ε), hε⟩
  · have h0 : normAtAllPlaces x ∈ (fun _ : {w : InfinitePlace K // w ≠ w₀} → ℝ ↦
        (0 : realSpace K)) '' aux4Box _ :=
      ⟨fun _ ↦ 0, mem_univ_pi.mpr fun _ ↦ ⟨le_refl 0, zero_le_one⟩, h.symm⟩
    obtain ⟨ε, hε⟩ := aux4_lift_cover h0
    exact mem_iUnion.mpr ⟨(Sum.inr (Sum.inr ()), ε), hε⟩

private theorem aux4_card_J : Fintype.card (aux4J K) = Module.finrank ℚ K - 1 := by
  have h₁ : Fintype.card {w : InfinitePlace K // w ≠ w₀} = Units.rank K := by
    rw [← Fintype.card_congr (equivFinRank (K := K)), Fintype.card_fin]
  have h₂ := card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h₃ := card_add_two_mul_card_eq_rank K
  have h₄ : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have h₅ : Fintype.card {w : InfinitePlace K // IsComplex w} = nrComplexPlaces K := rfl
  rw [Fintype.card_sum, h₁, h₅, Units.rank]
  omega

private theorem aux4_exists_lipschitz_cover_frontier_normLeOne (K : Type*) [Field K] [NumberField K] :
    ∃ (m : ℕ) (C : ℝ≥0) (f : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K),
      (∀ i, LipschitzOnWith C (f i) (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1)) ∧
      frontier (normLeOne K) ⊆
        ⋃ i, f i '' (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1) := by
  classical
  have hcard : Fintype.card (Fin (Module.finrank ℚ K - 1)) = Fintype.card (aux4J K) := by
    rw [Fintype.card_fin, aux4_card_J]
  let e : Fin (Module.finrank ℚ K - 1) ≃ aux4J K := Fintype.equivOfCardEq hcard
  let pre : (Fin (Module.finrank ℚ K - 1) → ℝ) → (aux4J K → ℝ) := fun y ↦ y ∘ e.symm
  have hpre_lip : LipschitzWith 1 pre := by
    intro y z
    rw [ENNReal.coe_one, one_mul, edist_pi_def, edist_pi_def]
    exact Finset.sup_le fun j _ ↦
      Finset.le_sup (f := fun b ↦ edist (y b) (z b)) (Finset.mem_univ (e.symm j))
  have hpre_maps : MapsTo pre (aux4Box _) (aux4Box _) := fun y hy ↦
    mem_univ_pi.mpr fun j ↦ mem_univ_pi.mp hy (e.symm j)
  have hpre_image : ∀ (g : (aux4J K → ℝ) → mixedSpace K),
      (g ∘ pre) '' aux4Box _ = g '' aux4Box _ := by
    intro g
    rw [image_comp]
    congr 1
    refine subset_antisymm (image_subset_iff.mpr hpre_maps) fun z hz ↦ ?_
    refine ⟨z ∘ e, mem_univ_pi.mpr fun j ↦ mem_univ_pi.mp hz (e j), ?_⟩
    ext j
    simp [pre]
  let eP := Fintype.equivFin (aux4CoverIdx K)
  choose Cp hCp using fun p : aux4CoverIdx K ↦
    aux4_exists_lipschitzOnWith_of_contDiff (aux4_contDiff_coverMap p)
  refine ⟨Fintype.card (aux4CoverIdx K), Finset.univ.sup Cp,
    fun i ↦ aux4CoverMap (eP.symm i) ∘ pre, fun i ↦ ?_, ?_⟩
  · have h := (hCp (eP.symm i)).comp (hpre_lip.lipschitzOnWith (s := aux4Box _)) hpre_maps
    rw [mul_one] at h
    exact h.weaken (Finset.le_sup (Finset.mem_univ _))
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (aux4_cover_mixed hx)
    refine mem_iUnion.mpr ⟨eP p, ?_⟩
    rw [hpre_image (aux4CoverMap (eP.symm (eP p))), eP.symm_apply_apply]
    exact hp

private theorem aux4_cover_transport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) {S : Set F} {d : ℕ}
    {m : ℕ} {C : ℝ≥0} {f : Fin m → (Fin d → ℝ) → F}
    (hf : ∀ i, LipschitzOnWith C (f i) (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1))
    (hcov : frontier S ⊆ ⋃ i, f i '' (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1)) :
    (∀ i, LipschitzOnWith (‖(e.symm : F →L[ℝ] E)‖₊ * C) ((e.symm : F → E) ∘ f i)
        (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1)) ∧
      frontier (e ⁻¹' S) ⊆ ⋃ i, ((e.symm : F → E) ∘ f i) ''
        (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1) := by
  constructor
  · exact fun i ↦ (e.symm : F →L[ℝ] E).lipschitz.comp_lipschitzOnWith (hf i)
  · have h₁ : frontier (e ⁻¹' S) = e ⁻¹' (frontier S) := by
      rw [← e.coe_toHomeomorph, ← Homeomorph.preimage_frontier]
    rw [h₁]
    intro x hx
    obtain ⟨i, y, hy, hxy⟩ := by simpa only [mem_iUnion, Set.mem_image] using hcov hx
    refine mem_iUnion.mpr ⟨i, y, hy, ?_⟩
    rw [Function.comp_apply, hxy, e.symm_apply_apply]

private theorem aux4_preimage_setOf_eq :
    {x : euclidean.mixedSpace K | x ∈ (euclidean.toMixed K) ⁻¹' (fundamentalCone K) ∧
      mixedEmbedding.norm ((euclidean.toMixed K) x) ≤ 1} =
        (euclidean.toMixed K) ⁻¹' (normLeOne K) := by
  ext x
  simp

private theorem aux4_exists_lipschitz_cover_frontier_preimage_toMixed
    (K : Type*) [Field K] [NumberField K] :
    ∃ (m : ℕ) (C : ℝ≥0) (f : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) →
        euclidean.mixedSpace K),
      (∀ i, LipschitzOnWith C (f i) (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1)) ∧
      frontier ((euclidean.toMixed K) ⁻¹' (normLeOne K)) ⊆
        ⋃ i, f i '' (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨m, C, f, hf, hcov⟩ := aux4_exists_lipschitz_cover_frontier_normLeOne K
  obtain ⟨hf', hcov'⟩ := aux4_cover_transport (euclidean.toMixed K) hf hcov
  exact ⟨m, _, _, hf', hcov'⟩

end NumberField.mixedEmbedding.fundamentalCone

end PART_R3

section PART_R1

section narR1

open Filter Ideal Asymptotics MeasureTheory Module Bornology Topology
p2m_open "NumberField P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.NumberField NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.NumberField.mixedEmbedding NumberField.Units NumberField.mixedEmbedding.euclidean NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.NumberField.mixedEmbedding.fundamentalCone Submodule"

open scoped nonZeroDivisors Real

namespace NumberField
p2m_export "NumberField" "classNumber_pos Units.rank discr mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice place mixedEmbedding InfinitePlace dedekindZeta_residue_def classNumber mixedEmbedding.norm mixedEmbedding.norm_smul dedekindZeta_residue"
namespace Ideal
p2m_export "NumberField.Ideal" "tendsto_norm_le_and_mk_eq_div_atTop"
p2m_open "NumberField.Ideal NumberField"

variable (K : Type*) [Field K] [NumberField K]

variable {C : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰} {s : ℝ}

private theorem narR1_aux₁ (hJ : ClassGroup.mk0 J = C⁻¹) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ ↦
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm

open Classical in

private def narR1_aux₂ :
    ↑({x | x ∈ (toMixed K) ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm ((toMixed K) x) ≤ s} ∩
      (ZLattice.comap ℝ (idealLattice K ((FractionalIdeal.mk0 K) J)) (toMixed K).toLinearMap))
        ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  rw [ZLattice.coe_comap]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.subtypeEquivProp ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ s)).symm
  ext
  simp_rw [mem_idealSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    mem_idealLattice, FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨_, ⟨⟨hx₁, hx₂⟩, _, ⟨x, hx₃, rfl⟩, h⟩, rfl⟩
    exact ⟨⟨hx₁, x, hx₃, h⟩, hx₂⟩
  · rintro ⟨⟨hx₁, ⟨x, hx₂, rfl⟩⟩, hx₃⟩
    exact ⟨(toMixed K).symm (mixedEmbedding K x), ⟨⟨hx₁, hx₃⟩, ⟨(x : K), by simp [hx₂], rfl⟩⟩, rfl⟩

private theorem narR1_tendsto_div_of_isBigO {u : ℝ → ℝ} {B θ : ℝ} (hθ : θ < 1)
    (h : (fun s ↦ u s - B * s) =O[atTop] fun s ↦ s ^ θ) :
    Tendsto (fun s ↦ u s / s) atTop (𝓝 B) := by
  have h1 : (fun s ↦ (u s - B * s) * s⁻¹) =O[atTop] fun s ↦ s ^ θ * s⁻¹ :=
    h.mul (isBigO_refl _ _)
  have h2 : Tendsto (fun s : ℝ ↦ s ^ θ * s⁻¹) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop (y := 1 - θ) (by linarith)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [← Real.rpow_neg_one, ← Real.rpow_add hs]
    congr 1
    ring
  have h3 := (h1.trans_tendsto h2).add_const B
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [div_eq_mul_inv, sub_mul, mul_inv_cancel_right₀ hs.ne', sub_add_cancel]

private theorem narR1_main (c : ClassGroup (𝓞 K)) :
    ∃ (θ : ℝ) (_hθ : θ < 1), (fun x : ℝ =>
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x
          ∧ ClassGroup.mk0 I = c} : ℝ)
          - (dedekindZeta_residue K / classNumber K) * x)
      =O[Filter.atTop] fun x => x ^ θ := by
  classical
  have hn : 0 < finrank ℚ K := finrank_pos
  have hθ : 1 - (finrank ℚ K : ℝ)⁻¹ < 1 := sub_lt_self 1 (inv_pos.mpr (Nat.cast_pos.mpr hn))
  refine ⟨1 - (finrank ℚ K : ℝ)⁻¹, hθ, ?_⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hNJ : 0 < (absNorm (J : Ideal (𝓞 K)) : ℝ) :=
    Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)
  have hw : (torsionOrder K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have h₁ : ∀ s : ℝ,
    {x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) ≤ s} =
      toMixed K ⁻¹' {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ s} := fun _ ↦ rfl
  have h₂ : {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1} = normLeOne K := by
    ext; simp

  obtain ⟨m, C, f, hf, hcov⟩ := aux4_exists_lipschitz_cover_frontier_preimage_toMixed K

  have hd : finrank ℚ K - 1 + 1 = finrank ℝ (euclidean.mixedSpace K) := by
    rw [euclidean.finrank, Nat.sub_add_cancel hn]
  have hR2 := ZLattice.covolume.isBigO_card_le_sub volume
    (ZLattice.comap ℝ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
      (toMixed K).toLinearMap)
    (X := (toMixed K) ⁻¹' (fundamentalCone K)) (F := fun x ↦ mixedEmbedding.norm (toMixed K x))
    (fun x r hx hr ↦ by rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem hr.ne'])
    (fun x r hr ↦ by
      rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg hr])
    ((toMixed K).antilipschitz.isBounded_preimage (isBounded_normLeOne K))
    ((toMixed K).continuous.measurable (measurableSet_normLeOne K))
    hd C f hf (by rw [h₁, h₂]; exact hcov)
  rw [euclidean.finrank] at hR2

  have hcount : ∀ s : ℝ,
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧
        ClassGroup.mk0 I = c} : ℝ) =
      (torsionOrder K : ℝ)⁻¹ * Nat.card ({x | x ∈ (toMixed K) ⁻¹' fundamentalCone K ∧
        mixedEmbedding.norm (toMixed K x) ≤ s * absNorm (J : Ideal (𝓞 K))} ∩
          (ZLattice.comap ℝ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
            (toMixed K).toLinearMap) : Set (euclidean.mixedSpace K)) := by
    intro s
    rw [narR1_aux₁ K hJ, Nat.card_congr (narR1_aux₂ K), ← card_isPrincipal_dvd_norm_le,
      Nat.cast_mul, inv_mul_eq_div, eq_div_iff hw]

  have hG := (hR2.comp_tendsto (tendsto_id.atTop_mul_const' hNJ))
  have hpow : (fun s : ℝ ↦ (id s * (absNorm (J : Ideal (𝓞 K)) : ℝ)) ^
      (1 - (finrank ℚ K : ℝ)⁻¹)) =O[atTop] fun s ↦ s ^ (1 - (finrank ℚ K : ℝ)⁻¹) := by
    refine IsBigO.of_bound ((absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (1 - (finrank ℚ K : ℝ)⁻¹)) ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    refine le_of_eq ?_
    rw [id_eq, Real.mul_rpow hs hNJ.le, norm_mul, mul_comm,
      Real.norm_of_nonneg (Real.rpow_nonneg hNJ.le _)]
  have hB := ((hG.trans hpow).const_mul_left ((torsionOrder K : ℝ)⁻¹)).congr_left
    (f₂ := fun s : ℝ ↦ (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ s ∧
        ClassGroup.mk0 I = c} : ℝ) - ((torsionOrder K : ℝ)⁻¹ *
          (volume.real {x | x ∈ (toMixed K) ⁻¹' fundamentalCone K ∧
            mixedEmbedding.norm (toMixed K x) ≤ 1} / ZLattice.covolume (ZLattice.comap ℝ
              (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
                (toMixed K).toLinearMap) volume) * absNorm (J : Ideal (𝓞 K))) * s)
    (fun s ↦ by simp only [Function.comp_apply, id_eq]; rw [hcount s]; ring)

  have hlimB := narR1_tendsto_div_of_isBigO hθ hB
  have hlimA := tendsto_norm_le_and_mk_eq_div_atTop K c
  have hres : (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
      (torsionOrder K * Real.sqrt |discr K|) = dedekindZeta_residue K / classNumber K := by
    have hh : (classNumber K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (classNumber_pos K).ne'
    rw [dedekindZeta_residue_def, div_div, mul_div_mul_right _ _ hh]
  rw [← hres, tendsto_nhds_unique hlimA hlimB]
  exact hB

end NumberField.Ideal

end narR1

section narR1_solution

p2m_open "NumberField P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.NumberField"

p2m_open_scoped "NumberField P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.NumberField nonZeroDivisors"

theorem solution
    (K : Type*) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    ∃ (θ : ℝ) (_hθ : θ < 1), (fun x : ℝ =>
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x
          ∧ ClassGroup.mk0 I = c} : ℝ)
          - (dedekindZeta_residue K / classNumber K) * x)
      =O[Filter.atTop] fun x => x ^ θ :=
  NumberField.Ideal.narR1_main K c

end narR1_solution

end PART_R1

end

end S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub
end P2MW
export P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub (solution)
