-- Prove2me | solution 1 for MasulloGRH.rposModulated_isGoodSubgroup_bot
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:52.090077+00:00
-- url     : https://prove2.me/submissions/434fd92e-8633-4760-9160-18ce2fcd36b7

import Mathlib
import Definitions.Def_MasulloGRH_ExpDecaySpaces
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
import Theorems.Thm_MasulloGRH_compactlyGenerated_exists_elemQuotient
import Theorems.Thm_MasulloGRH_annihilator_isCompactlyGenerated
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact

set_option autoImplicit false

namespace MasulloGRHBotGoodAux

open MasulloGRH Topology Set Filter

lemma circle_nss (z : UnitAddCircle) (h : ∀ k : ℕ, ‖k • z‖ < 1 / 4) : z = 0 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, |t| ≤ 1 / 2 ∧ (t : UnitAddCircle) = z := by
    refine ⟨(AddCircle.equivIoc 1 (-1 / 2) z : ℝ), ?_, ?_⟩
    · have h1 := (AddCircle.equivIoc 1 (-1 / 2) z).2
      rw [abs_le]
      constructor
      · linarith [h1.1]
      · linarith [h1.2]
    · exact (AddCircle.equivIoc 1 (-1 / 2)).symm_apply_apply z
  have hn : ∀ x : ℝ, |x| ≤ 1 / 2 → ‖(x : UnitAddCircle)‖ = |x| := fun x hx =>
    (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).2 (by simpa using hx)
  by_contra hz
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hz (by simp)
  have hpos : 0 < |t| := abs_pos.2 ht0
  have h1 := h 1
  rw [one_smul, hn t ht] at h1
  set k := Nat.ceil (1 / (4 * |t|)) with hkdef
  have hk1 : 1 / (4 * |t|) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < 1 / (4 * |t|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hA : 1 / 4 ≤ (k : ℝ) * |t| := by
    have := mul_le_mul_of_nonneg_right hk1 hpos.le
    have e : 1 / (4 * |t|) * |t| = 1 / 4 := by field_simp
    linarith
  have hB : (k : ℝ) * |t| < 1 / 2 := by
    have := mul_lt_mul_of_pos_right hk2 hpos
    have e : (1 / (4 * |t|) + 1) * |t| = 1 / 4 + |t| := by field_simp
    linarith
  have hk := h k
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, hn _ (by rw [abs_mul, Nat.abs_cast]; linarith),
    abs_mul, Nat.abs_cast] at hk
  linarith

lemma circle_subgroup_nss : ∃ S : Set Circle, IsOpen S ∧ (1 : Circle) ∈ S ∧
    ∀ H : Subgroup Circle, (H : Set Circle) ⊆ S → H = ⊥ := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : ∀ t : UnitAddCircle, e t = AddCircle.toCircle t := fun t =>
    AddCircle.homeomorphCircle_apply _ t
  have he0 : e 0 = 1 := by
    rw [he]
    simpa using AddCircle.toCircle_nsmul (0 : UnitAddCircle) 0
  refine ⟨e '' Metric.ball 0 (1 / 4), e.isOpenMap _ Metric.isOpen_ball,
    ⟨0, Metric.mem_ball_self (by norm_num), he0⟩, ?_⟩
  intro H hH
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨t, -, rfl⟩ := hH hz
  have ht : t = 0 := by
    apply circle_nss
    intro j
    obtain ⟨t', ht', hte⟩ := hH (H.pow_mem hz j)
    have : t' = j • t := by
      apply e.injective
      rw [hte, he, he, AddCircle.toCircle_nsmul]
    subst this
    simpa [Metric.mem_ball, dist_zero_right] using ht'
  subst ht
  rw [he0]
  exact Subgroup.one_mem _

variable {G : Type*} [CommGroup G] [TopologicalSpace G] {m : G → ℝ}

lemma m_one (hm : IsModule m) : m 1 = 1 := by
  have h := hm.map_mul 1 1
  rw [mul_one] at h
  have hp := hm.pos 1
  field_simp at h
  linarith [h]

lemma m_inv (hm : IsModule m) (g : G) : m g⁻¹ = (m g)⁻¹ := by
  have h := hm.map_mul g g⁻¹
  rw [mul_inv_cancel, m_one hm] at h
  have hp := hm.pos g
  field_simp
  linarith [h]

/-- A modulated group is compactly generated. -/
lemma cg_of_rpos (hm : IsRposModule m) : ∃ C : Set G, IsCompact C ∧ Subgroup.closure C = ⊤ := by
  refine ⟨m ⁻¹' Set.Icc (1 / 2) 2, hm.1.proper _ _ (by norm_num), ?_⟩
  let φ : G →* ℝ := { toFun := m, map_one' := m_one hm.1, map_mul' := hm.1.map_mul }
  have hφ : ∀ g, φ g = m g := fun _ => rfl
  obtain ⟨h, hh⟩ := hm.2 2 (by norm_num)
  have hhC : h ∈ Subgroup.closure (m ⁻¹' Set.Icc (1 / 2) 2) :=
    Subgroup.subset_closure (by simp [hh]; norm_num)
  rw [eq_top_iff]
  intro g _
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (hm.1.pos g) (show (1 : ℝ) < 2 by norm_num)
  have hz : m (h ^ n) = 2 ^ n := by
    rw [← hφ, MonoidHom.map_zpow' φ (fun x => m_inv hm.1 x), hφ, hh]
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hmem : g * (h ^ n)⁻¹ ∈ Subgroup.closure (m ⁻¹' Set.Icc (1 / 2) 2) := by
    apply Subgroup.subset_closure
    simp only [Set.mem_preimage, Set.mem_Icc]
    rw [hm.1.map_mul, m_inv hm.1, hz]
    rw [zpow_add_one₀ (by norm_num)] at hn2
    constructor
    · have : (1 : ℝ) ≤ m g * (2 ^ n)⁻¹ := by
        rw [le_mul_inv_iff₀ hpos]; linarith
      linarith
    · rw [mul_inv_le_iff₀ hpos]; linarith
  have : g = g * (h ^ n)⁻¹ * h ^ n := by simp
  rw [this]
  exact Subgroup.mul_mem _ hmem (Subgroup.zpow_mem _ hhC n)

end MasulloGRHBotGoodAux

open MasulloGRH MasulloGRHBotGoodAux Topology Set in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (G1 : Subgroup G) (hG1 : ∀ g : G, g ∈ G1 ↔ m g = 1)
    (hcg : IsCompactlyGeneratedSubgroup (⊤ : Subgroup (PontryaginDual G1))) :
    IsGoodSubgroup (⊥ : Subgroup G) := by
  obtain ⟨hG1c, hG1le⟩ := isCompact_moduleKernel_and_compact_le G m hm G1 hG1
  haveI : CompactSpace ↥G1 := isCompact_iff_compactSpace.mp hG1c
  obtain ⟨F, hFc, -, -, hFcl⟩ := hcg
  have hFfin : F.Finite := hFc.finite_of_discrete
  obtain ⟨S, hSo, hS1, hSH⟩ := circle_subgroup_nss
  -- the neighbourhood on which the generating characters are small
  let W : Set ↥G1 := ⋂ χ ∈ F, (fun x : ↥G1 => χ x) ⁻¹' S
  have hWo : IsOpen W := hFfin.isOpen_biInter fun χ _ => hSo.preimage χ.continuous_toFun
  have hW1 : (1 : ↥G1) ∈ W := by
    simp only [W, mem_iInter, mem_preimage]
    intro χ _
    rw [map_one]; exact hS1
  obtain ⟨U₀, hU₀o, hU₀W⟩ := isOpen_induced_iff.1 hWo
  have hU₀1 : (1 : G) ∈ U₀ := by
    have : (1 : ↥G1) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀W]; exact hW1
    exact this
  obtain ⟨K, hKc, hKU, a, n, r, s, d, π, hd, hπc, hπo, hπs, hπk⟩ :=
    compactlyGenerated_exists_elemQuotient G (cg_of_rpos hm) U₀ (hU₀o.mem_nhds hU₀1)
  have hKG1 : K ≤ G1 := hG1le K hKc
  -- every character of `G1` is trivial on `K`
  have hF : ∀ χ ∈ F, ∀ x : ↥G1, (x : G) ∈ K → χ x = 1 := by
    intro χ hχ x hx
    have hbot := hSH ((K.subgroupOf G1).map χ.toMonoidHom) (by
      rintro _ ⟨y, hy, rfl⟩
      have hyW : y ∈ W := by
        rw [← hU₀W]; exact hKU (Subgroup.mem_subgroupOf.1 hy)
      have := mem_iInter₂.1 hyW χ hχ
      exact this)
    have hmem : χ.toMonoidHom x ∈ (K.subgroupOf G1).map χ.toMonoidHom :=
      ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hbot] at hmem
    exact hmem
  have hall : ∀ χ : PontryaginDual ↥G1, ∀ x : ↥G1, (x : G) ∈ K → χ x = 1 := by
    intro χ
    have hχ : χ ∈ Subgroup.closure F := by rw [hFcl]; trivial
    induction hχ using Subgroup.closure_induction with
    | mem χ h => exact hF χ h
    | one => intro x _; rfl
    | mul χ ψ _ _ h1 h2 =>
      intro x hx
      show χ x * ψ x = 1
      rw [h1 x hx, h2 x hx, mul_one]
    | inv χ _ h1 =>
      intro x hx
      show (χ x)⁻¹ = 1
      rw [h1 x hx, inv_one]
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hne
    let y : ↥G1 := ⟨x, hKG1 hx⟩
    have hy : y ∉ (⊥ : Subgroup ↥G1) := by
      rw [Subgroup.mem_bot]
      intro h
      exact hne (congrArg Subtype.val h)
    obtain ⟨χ, -, hχ⟩ := pontryaginDual_separates_of_locallyCompact ↥G1 ⊥
      (by simpa using isClosed_singleton) y hy
    exact hχ (hall χ y hx)
  subst hKbot
  -- the presentation of `⊤ / ⊥`
  have hpres : IsElemPresentation (⊤ : Subgroup G) ⊥ (π.comp (⊤ : Subgroup G).subtype) := by
    refine ⟨hd, hπc.comp continuous_subtype_val, ?_, ?_, ?_⟩
    · have : IsOpenMap (Subtype.val : ↥(⊤ : Subgroup G) → G) :=
        IsOpen.isOpenMap_subtype_val (by simp)
      exact hπo.comp this
    · intro y
      obtain ⟨x, rfl⟩ := hπs y
      exact ⟨⟨x, trivial⟩, rfl⟩
    · intro x
      exact hπk x
  refine ⟨by simpa using isClosed_singleton, ?_, ?_⟩
  · have : annihilator (⊥ : Subgroup G) = Set.univ := by
      ext χ
      simp [annihilator]
    rw [this]; exact isOpen_univ
  · exact annihilator_isCompactlyGenerated G ⊥ ⊤ (by simp) (by simp) bot_le _ hpres
