-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/af2a4bd1-03d5-5cb5-932c-6efa33317862

import Mathlib
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Topology

namespace HurTc

theorem complex_eq_one_of_norm_eq_one_of_forall_re_pow_two_pow_pos (z : ℂ) (hz : ‖z‖ = 1)
    (h : ∀ k : ℕ, 0 < (z ^ (2 ^ k)).re) : z = 1 := by
  have hnorm : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hsum : ∀ k : ℕ, (z ^ (2 ^ k)).re * (z ^ (2 ^ k)).re + (z ^ (2 ^ k)).im * (z ^ (2 ^ k)).im = 1 := by
    intro k
    have h1 := Complex.normSq_eq_norm_sq (z ^ (2 ^ k))
    rw [Complex.normSq_apply, hnorm, one_pow] at h1
    exact h1
  have hrec : ∀ k : ℕ, (z ^ (2 ^ (k + 1))).re = 2 * (z ^ (2 ^ k)).re ^ 2 - 1 := by
    intro k
    have hsq : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k) := by rw [pow_succ, pow_mul, sq]
    rw [hsq, Complex.mul_re]
    have := hsum k
    nlinarith [this]
  have hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1 := fun k =>
    ((abs_le.mp (Complex.abs_re_le_norm (z ^ (2 ^ k)))).2).trans (hnorm k).le
  have hgap : ∀ k : ℕ, (2 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [hrec, pow_succ]
        have hpos := h k
        have hle1 := hle k
        nlinarith [ih, hpos, hle1]
  have hre : z.re = 1 := by
    by_contra hne
    have hle0 : z.re ≤ 1 := by simpa using hle 0
    have hlt : z.re < 1 := lt_of_le_of_ne hle0 hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 2)
    have hpos := h k
    have hg := hgap k
    have h1 : 1 < (2 : ℝ) ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ (by linarith)] at hk
      linarith
    linarith
  have him : z.im = 0 := by
    have h1 := hsum 0
    simp only [pow_zero, pow_one] at h1
    rw [hre] at h1
    have : z.im * z.im = 0 := by linarith
    exact mul_self_eq_zero.mp this
  exact Complex.ext (by rw [hre, Complex.one_re]) (by rw [him, Complex.one_im])

section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def unitSphere : Subgroup (v.adicCompletion K)ˣ where
  carrier := {t | Valued.v (t : v.adicCompletion K) = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

theorem mem_unitSphere_iff (t : (v.adicCompletion K)ˣ) :
    t ∈ unitSphere K v ↔ Valued.v (t : v.adicCompletion K) = 1 := Iff.rfl

theorem sphere_eq :
    {x : v.adicCompletion K | (Valued.v).restrict x = 1} = {x : v.adicCompletion K | Valued.v x = 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Valuation.restrict_eq_one_iff]

theorem isClosed_sphere_one : IsClosed {x : v.adicCompletion K | Valued.v x = 1} := by
  rw [← sphere_eq]
  exact Valued.isClosed_sphere (R := v.adicCompletion K) 1

theorem isOpen_sphere_one : IsOpen {x : v.adicCompletion K | Valued.v x = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  have h := Valued.locally_const (R := v.adicCompletion K) (x := x) (by rw [hx]; exact one_ne_zero)
  rw [hx] at h
  exact h

theorem isCompact_sphere_one : IsCompact {x : v.adicCompletion K | Valued.v x = 1} := by
  refine (NumberField.isCompactAdicCompletionIntegers K v).of_isClosed_subset (isClosed_sphere_one K v) ?_
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hx

theorem val_image_unitSphere :
    Units.val '' (unitSphere K v : Set (v.adicCompletion K)ˣ) = {x : v.adicCompletion K | Valued.v x = 1} := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    have hx0 : x ≠ 0 := by
      intro h0
      rw [Set.mem_setOf_eq, h0, map_zero] at hx
      exact zero_ne_one hx
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem isCompact_unitSphere : IsCompact (unitSphere K v : Set (v.adicCompletion K)ˣ) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, val_image_unitSphere]
  exact isCompact_sphere_one K v

theorem isOpen_unitSphere : IsOpen (unitSphere K v : Set (v.adicCompletion K)ˣ) :=
  (isOpen_sphere_one K v).preimage Units.continuous_val

theorem norm_apply_eq_one_of_mem_unitSphere
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous fun t : (v.adicCompletion K)ˣ => ((χ t : ℂˣ) : ℂ))
    (t : (v.adicCompletion K)ˣ) (ht : t ∈ unitSphere K v) : ‖((χ t : ℂˣ) : ℂ)‖ = 1 := by
  set f : (v.adicCompletion K)ˣ → ℝ := fun t => ‖((χ t : ℂˣ) : ℂ)‖ with hf
  have hfc : Continuous f := continuous_norm.comp hχ
  have hfpow : ∀ (a : (v.adicCompletion K)ˣ) (n : ℕ), f (a ^ n) = f a ^ n := by
    intro a n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hfinv : ∀ a : (v.adicCompletion K)ˣ, f a⁻¹ = (f a)⁻¹ := by
    intro a
    simp only [hf, map_inv, Units.val_inv_eq_inv_val, norm_inv]
  have hfpos : ∀ a : (v.adicCompletion K)ˣ, 0 < f a := fun a => norm_pos_iff.mpr (χ a).ne_zero
  obtain ⟨M, hM⟩ := ((isCompact_unitSphere K v).image hfc).bddAbove
  have hle : ∀ s ∈ unitSphere K v, f s ≤ 1 := by
    intro s hs
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
    have hmem : f (s ^ n) ∈ f '' (unitSphere K v : Set (v.adicCompletion K)ˣ) := ⟨s ^ n, pow_mem hs n, rfl⟩
    have hb := hM hmem
    rw [hfpow] at hb
    linarith
  have h1 := hle t ht
  have h2 := hle t⁻¹ (inv_mem ht)
  rw [hfinv, inv_le_one₀ (hfpos t)] at h2
  exact le_antisymm h1 h2

theorem exists_isOpen_subgroup_apply_eq_one
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous fun t : (v.adicCompletion K)ˣ => ((χ t : ℂˣ) : ℂ)) :
    ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧ ∀ t ∈ U, χ t = 1 := by
  haveI : CompactSpace (unitSphere K v) := isCompact_iff_compactSpace.mp (isCompact_unitSphere K v)
  let ι : unitSphere K v → v.adicCompletion K := fun s => ((s : (v.adicCompletion K)ˣ) : v.adicCompletion K)
  have hι : Topology.IsEmbedding ι := Units.isEmbedding_val₀.comp Topology.IsEmbedding.subtypeVal

  set W₀ : Set (unitSphere K v) := {s | 0 < (((χ (s : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ)).re} with hW₀def
  have hW₀open : IsOpen W₀ :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (hχ.comp continuous_subtype_val))
  have h1W₀ : (1 : unitSphere K v) ∈ W₀ := by
    simp [hW₀def]
  have hW₀ : W₀ ∈ 𝓝 (1 : unitSphere K v) := hW₀open.mem_nhds h1W₀
  rw [hι.isInducing.nhds_eq_comap, Filter.mem_comap] at hW₀
  obtain ⟨t, ht, hsub⟩ := hW₀
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht

  set W : Set (unitSphere K v) := ι ⁻¹' {y : v.adicCompletion K | (Valued.v).restrict (y - ι 1) < γ.1} with hWdef
  have hWclopen : IsClopen W := by
    have hb : IsClopen {y : v.adicCompletion K | (Valued.v).restrict (y - ι 1) < γ.1} :=
      (Valued.isClopen_ball (R := v.adicCompletion K) γ.1).preimage (continuous_sub_right (ι 1))
    exact hb.preimage hι.continuous
  have h1W : (1 : unitSphere K v) ∈ W := by
    show (Valued.v).restrict (ι 1 - ι 1) < γ.1
    rw [sub_self, map_zero]
    exact zero_lt_iff.mpr γ.ne_zero
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hWclopen h1W
  have hHW₀ : ∀ s : unitSphere K v, s ∈ (H : Subgroup (unitSphere K v)) → s ∈ W₀ :=
    fun s hs => hsub (hγ (hH hs))
  refine ⟨(H : Subgroup (unitSphere K v)).map (unitSphere K v).subtype, ?_, ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact (isOpen_unitSphere K v).isOpenMap_subtype_val _ H.isOpen
  · rintro t ⟨s, hs, rfl⟩
    have hall : ∀ k : ℕ, 0 < ((((χ (s : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ)) ^ (2 ^ k)).re := by
      intro k
      have hk := hHW₀ _ (pow_mem hs (2 ^ k))
      simp only [hW₀def, Set.mem_setOf_eq, Subgroup.coe_pow, map_pow, Units.val_pow_eq_pow_val] at hk
      exact hk
    have hn1 : ‖((χ (s : (v.adicCompletion K)ˣ) : ℂˣ) : ℂ)‖ = 1 :=
      norm_apply_eq_one_of_mem_unitSphere K v χ hχ _ s.2
    have hz := complex_eq_one_of_norm_eq_one_of_forall_re_pow_two_pow_pos _ hn1 hall
    exact Units.val_eq_one.mp hz

end

end HurTc

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous fun t : (v.adicCompletion K)ˣ => ((χ t : ℂˣ) : ℂ)) :
    (∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → ‖((χ t : ℂˣ) : ℂ)‖ = 1) ∧
    ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧ ∀ t ∈ U, χ t = 1 :=
  ⟨fun t ht => HurTc.norm_apply_eq_one_of_mem_unitSphere K v χ hχ t ht,
    HurTc.exists_isOpen_subgroup_apply_eq_one K v χ hχ⟩

end S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one (solution)
