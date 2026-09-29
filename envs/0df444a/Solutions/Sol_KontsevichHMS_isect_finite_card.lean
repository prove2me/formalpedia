-- Prove2me | solution 1 for KontsevichHMS.isect_finite_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:07:33.495908+00:00
-- url     : https://prove2.me/submissions/dbbea4ee-4f5e-44ea-96a8-e22ac242c171

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

set_option autoImplicit false

open KontsevichHMS KontsevichHMS.Brane in
theorem k79522c41_ac_eq_iff (x y : ℝ) :
    ((x : AddCircle (1:ℝ)) = (y : AddCircle (1:ℝ))) ↔ ∃ k : ℤ, x - y = k := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, mul_one]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.symm⟩

open KontsevichHMS KontsevichHMS.Brane in
theorem k79522c41_proj_eq_iff (x y : ℝ × ℝ) :
    proj x = proj y ↔ (∃ k : ℤ, x.1 - y.1 = k) ∧ ∃ k : ℤ, x.2 - y.2 = k := by
  unfold proj
  rw [Prod.mk.injEq, k79522c41_ac_eq_iff, k79522c41_ac_eq_iff]

open KontsevichHMS KontsevichHMS.Brane in
theorem k79522c41_mem_line (b : Brane) (z : Torus) :
    z ∈ b.line ↔ ∃ (t : ℝ) (g : ℤ × ℤ),
      proj (b.base + t • b.dirR + ((g.1 : ℝ), (g.2 : ℝ))) = z := by
  unfold line liftLine
  constructor
  · rintro ⟨x, ⟨t, g, rfl⟩, hx⟩
    exact ⟨t, g, hx⟩
  · rintro ⟨t, g, hx⟩
    exact ⟨_, ⟨t, g, rfl⟩, hx⟩


open KontsevichHMS KontsevichHMS.Brane in
theorem solution (b₁ b₂ : Brane) (h : Transverse b₁ b₂) :
    ∃ hfin : (isect b₁ b₂).Finite,
      hfin.toFinset.card = (b₁.dir.1 * b₂.dir.2 - b₁.dir.2 * b₂.dir.1).natAbs := by
  classical
  set D : ℤ := b₁.dir.1 * b₂.dir.2 - b₁.dir.2 * b₂.dir.1 with hDdef
  have hD : (D : ℝ) ≠ 0 := by
    unfold Transverse det2 dirR at h
    rw [hDdef]; push_cast; exact h
  have hD0 : D ≠ 0 := by exact_mod_cast hD
  set c : ℝ := (b₂.base.1 - b₁.base.1) * (b₂.dir.2 : ℝ) - (b₂.base.2 - b₁.base.2) * (b₂.dir.1 : ℝ)
    with hc
  set F : ℤ → Torus := fun j => proj (b₁.base + ((c + j) / (D : ℝ)) • b₁.dirR) with hF
  -- every `F j` is an intersection point
  have h1 : ∀ j : ℤ, F j ∈ isect b₁ b₂ := by
    intro j
    refine ⟨(k79522c41_mem_line b₁ _).2 ⟨(c + j) / (D : ℝ), (0, 0), ?_⟩,
      (k79522c41_mem_line b₂ _).2 ?_⟩
    · simp only [hF]
      congr 1
      ext <;> simp
    · obtain ⟨a, b, hab⟩ := b₂.dir_primitive
      have hab' : (a : ℝ) * b₂.dir.1 + b * b₂.dir.2 = 1 := by exact_mod_cast hab
      refine ⟨-((b₁.dir.1 : ℝ) * (b₂.base.2 - b₁.base.2 + ((-(j * a) : ℤ) : ℝ))
          - (b₁.dir.2 : ℝ) * (b₂.base.1 - b₁.base.1 + ((j * b : ℤ) : ℝ))) / (D : ℝ),
        (j * b, -(j * a)), ?_⟩
      simp only [hF]
      congr 1
      ext
      · simp only [dirR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rw [hDdef] at hD ⊢
        push_cast at hD ⊢
        field_simp
        linear_combination (b₁.dir.1 * (j : ℝ)) * hab'
      · simp only [dirR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [hDdef] at hD ⊢
        push_cast at hD ⊢
        field_simp
        linear_combination (b₁.dir.2 * (j : ℝ)) * hab'
  have h2 : ∀ z ∈ isect b₁ b₂, ∃ j : ℤ, F j = z := by
    rintro z ⟨hz1, hz2⟩
    obtain ⟨t1, g1, e1⟩ := (k79522c41_mem_line b₁ z).1 hz1
    obtain ⟨t2, g2, e2⟩ := (k79522c41_mem_line b₂ z).1 hz2
    obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := (k79522c41_proj_eq_iff _ _).1 (e1.trans e2.symm)
    simp only [dirR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hk1 hk2
    refine ⟨(g2.1 - g1.1 + k1) * b₂.dir.2 - (g2.2 - g1.2 + k2) * b₂.dir.1, ?_⟩
    have ht1 : t1 = (c + (((g2.1 - g1.1 + k1) * b₂.dir.2 - (g2.2 - g1.2 + k2) * b₂.dir.1 : ℤ)
        : ℝ)) / (D : ℝ) := by
      rw [eq_div_iff hD, hc, hDdef]
      push_cast
      linear_combination (b₂.dir.2 : ℝ) * hk1 - (b₂.dir.1 : ℝ) * hk2
    rw [← e1, hF]
    simp only
    rw [← ht1]
    refine (k79522c41_proj_eq_iff _ _).2 ⟨⟨-g1.1, ?_⟩, ⟨-g1.2, ?_⟩⟩
    · simp only [dirR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; push_cast; ring
    · simp only [dirR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; push_cast; ring
  have h3 : ∀ j k : ℤ, F (j + D * k) = F j := by
    intro j k
    simp only [hF]
    refine (k79522c41_proj_eq_iff _ _).2 ⟨⟨k * b₁.dir.1, ?_⟩, ⟨k * b₁.dir.2, ?_⟩⟩
    · simp only [dirR, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; push_cast; field_simp; ring
    · simp only [dirR, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; push_cast; field_simp; ring
  obtain ⟨a1, b1', hab1⟩ := b₁.dir_primitive
  have hab1' : (a1 : ℝ) * b₁.dir.1 + b1' * b₁.dir.2 = 1 := by exact_mod_cast hab1
  have h4 : ∀ j j' : ℤ, F j = F j' → D ∣ j - j' := by
    intro j j' hjj
    simp only [hF] at hjj
    obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := (k79522c41_proj_eq_iff _ _).1 hjj
    simp only [dirR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hk1 hk2
    have hsD : ((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * D = j - j' := by field_simp; ring
    have hk1' : ((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * b₁.dir.1 = k1 := by
      linear_combination hk1
    have hk2' : ((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * b₁.dir.2 = k2 := by
      linear_combination hk2
    have hR : ((j - j' : ℤ) : ℝ) = ((a1 * k1 + b1' * k2 : ℤ) : ℝ) * (D : ℝ) := by
      push_cast
      linear_combination (-1 : ℝ) * hsD + ((a1 : ℝ) * D) * hk1' + ((b1' : ℝ) * D) * hk2'
        - (((c + j) / (D:ℝ) - (c + j') / (D:ℝ)) * D) * hab1'
    have hZ : j - j' = (a1 * k1 + b1' * k2) * D := by exact_mod_cast hR
    exact ⟨a1 * k1 + b1' * k2, by rw [hZ]; ring⟩
  set n : ℕ := D.natAbs with hn
  have hset : isect b₁ b₂ = F '' ((Finset.Ico (0:ℤ) (n:ℤ) : Finset ℤ) : Set ℤ) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, rfl⟩ := h2 z hz
      refine ⟨j % D, ?_, ?_⟩
      · simp only [Finset.coe_Ico, Set.mem_Ico]
        refine ⟨Int.emod_nonneg _ hD0, ?_⟩
        exact Int.emod_lt j hD0
      · have := h3 (j % D) (j / D)
        rw [Int.emod_add_mul_ediv] at this
        exact this.symm
    · rintro ⟨j, -, rfl⟩
      exact h1 j
  have hinj : Set.InjOn F ((Finset.Ico (0:ℤ) (n:ℤ) : Finset ℤ) : Set ℤ) := by
    intro j hj j' hj' hjj
    simp only [Finset.coe_Ico, Set.mem_Ico] at hj hj'
    have hdvd := h4 j j' hjj
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
    omega
  have hfin : (isect b₁ b₂).Finite := by
    rw [hset]
    exact (Finset.finite_toSet _).image F
  refine ⟨hfin, ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hfin, hset, hinj.ncard_image,
    Set.ncard_coe_finset, Int.card_Ico]
  simp
