-- Prove2me | solution 1 for MasulloGRH.exists_cofinal_structuralPairs
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T14:02:44.033273+00:00
-- url     : https://prove2.me/submissions/0b4d8abe-5c44-4b4b-a9cc-5417d29c70d4

import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_exists_small_good_subgroups

set_option autoImplicit false

namespace Aux_CF

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

lemma elem_nss (m n r s : ℕ) (d : Fin s → ℕ) :
    ∃ V ∈ 𝓝 (0 : ElemGroup m n r s d),
      ∀ x : ElemGroup m n r s d, (∀ k : ℕ, k • x ∈ V) → x = 0 := by
  refine ⟨Metric.ball (0 : Fin m → ℝ) 1 ×ˢ (Metric.ball (0 : Fin n → UnitAddCircle) (1 / 4) ×ˢ
    (({0} : Set (Fin r → ℤ)) ×ˢ ({0} : Set ((i : Fin s) → ZMod (d i))))), ?_, ?_⟩
  · refine prod_mem_nhds (Metric.ball_mem_nhds _ one_pos)
      (prod_mem_nhds (Metric.ball_mem_nhds _ (by norm_num)) (prod_mem_nhds ?_ ?_))
    · exact (isOpen_discrete _).mem_nhds rfl
    · exact (isOpen_discrete _).mem_nhds rfl
  · rintro ⟨a, b, c, e⟩ h
    have ha : a = 0 := by
      by_contra ha
      have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ‖a‖)
      have h1 : ‖k • a‖ < 1 := by
        have := (h k).1
        simpa [Metric.mem_ball, dist_zero_right] using this
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at h1
      rw [div_lt_iff₀ hpos] at hk
      linarith
    have hb : b = 0 := by
      funext j
      refine circle_nss (b j) fun k => ?_
      have h1 : ‖k • b‖ < 1 / 4 := by
        have := (h k).2.1
        simpa [Metric.mem_ball, dist_zero_right] using this
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm (k • b) j) h1
    have hc : c = 0 := by simpa using (h 1).2.2.1
    have he : e = 0 := by simpa using (h 1).2.2.2
    subst ha hb hc he
    rfl

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma pair_nss {Γ k : Subgroup G} {m n r s : ℕ} {d : Fin s → ℕ}
    {π : ↥Γ →* Multiplicative (ElemGroup m n r s d)} (hΓ : IsOpen (Γ : Set G))
    (hπ : IsElemPresentation Γ k π) :
    ∃ W ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ W → H ≤ k := by
  obtain ⟨V, hV, hVx⟩ := elem_nss m n r s d
  let O : Set ↥Γ := {y | Multiplicative.toAdd (π y) ∈ V}
  have hO : O ∈ 𝓝 (1 : ↥Γ) := by
    have hc : Continuous (fun y : ↥Γ => Multiplicative.toAdd (π y)) :=
      continuous_toAdd.comp hπ.2.1
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  refine ⟨Subtype.val '' O, ?_, ?_⟩
  · exact hΓ.isOpenMap_subtype_val.image_mem_nhds hO
  · intro H hH x hx
    obtain ⟨y, -, rfl⟩ := hH hx
    have h0 : Multiplicative.toAdd (π y) = 0 := by
      apply hVx
      intro j
      obtain ⟨z, hzO, hz⟩ := hH (H.pow_mem hx j)
      have hzy : z = y ^ j := Subtype.ext (by simp [hz])
      subst hzy
      have h2 : Multiplicative.toAdd (π (y ^ j)) ∈ V := hzO
      simpa [map_pow, toAdd_pow] using h2
    exact (hπ.2.2.2.2 y).1 (by simpa using h0)

end Aux_CF

open MasulloGRH Topology Set Filter in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ (Γ k : ℕ → Subgroup G) (m n r s : ℕ → ℕ) (d : (N : ℕ) → Fin (s N) → ℕ)
      (π : (N : ℕ) → ↥(Γ N) →* Multiplicative (ElemGroup (m N) (n N) (r N) (s N) (d N))),
      (∀ N, IsStructuralPair (Γ N) (k N) ∧ IsElemPresentation (Γ N) (k N) (π N)) ∧
      Monotone Γ ∧ Antitone k ∧
      ∀ (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
        (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')),
        IsStructuralPair Γ' k' → IsElemPresentation Γ' k' π' → ∃ M, Γ' ≤ Γ M ∧ k M ≤ k' := by
  obtain ⟨k₀, hanti, hsmall, hgood, hpres⟩ := exists_small_good_subgroups G
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨N₀, hN₀⟩ := hsmall V hV
  let k : ℕ → Subgroup G := fun N => k₀ (N + N₀)
  have hk_anti : Antitone k := fun a b h => hanti (by omega)
  have hkV : ∀ N, (k N : Set G) ⊆ V := fun N x hx =>
    hN₀ (hanti (by omega : N₀ ≤ N + N₀) hx)
  let C : ℕ → Set G := fun N => V ∪ compactCovering G N
  let Γ : ℕ → Subgroup G := fun N => Subgroup.closure (C N)
  have hCc : ∀ N, IsCompact (C N) := fun N => hVc.union (isCompact_compactCovering G N)
  have hΓmono : Monotone Γ := fun a b h =>
    Subgroup.closure_mono (union_subset_union_right _ (compactCovering_subset G h))
  have hCΓ : ∀ N, C N ⊆ Γ N := fun N => Subgroup.subset_closure
  have hVΓ : ∀ N, V ⊆ Γ N := fun N => subset_union_left.trans (hCΓ N)
  have hΓopen : ∀ N, IsOpen (Γ N : Set G) := fun N =>
    Subgroup.isOpen_of_mem_nhds (Γ N) (Filter.mem_of_superset hV (hVΓ N))
  have hΓcg : ∀ N, IsCompactlyGeneratedSubgroup (Γ N) := fun N =>
    ⟨C N, hCc N, hCΓ N, ⟨V, hV, inter_subset_left.trans subset_union_left⟩, rfl⟩
  have hkΓ : ∀ N, k N ≤ Γ N := fun N x hx => hVΓ N (hkV N hx)
  have hex : ∀ N, ∃ (m n r s : ℕ) (d : Fin s → ℕ)
      (π : ↥(Γ N) →* Multiplicative (ElemGroup m n r s d)), IsElemPresentation (Γ N) (k N) π :=
    fun N => hpres (N + N₀) (Γ N) (hΓopen N) (hΓcg N) (hkΓ N)
  choose m n r s d π hπ using hex
  refine ⟨Γ, k, m, n, r, s, d, π, fun N => ⟨⟨hΓopen N, hΓcg N, hgood _, hkΓ N⟩, hπ N⟩,
    hΓmono, hk_anti, ?_⟩
  intro Γ' k' m' n' r' s' d' π' hs' hπ'
  obtain ⟨U', hU'c, -, -, hU'cl⟩ := hs'.2.1
  have hdir : Directed (· ⊆ ·) (fun N => (Γ N : Set G)) :=
    (show Monotone (fun N => (Γ N : Set G)) from fun a b h => hΓmono h).directed_le
  obtain ⟨M, hM⟩ := hU'c.elim_directed_cover (fun N => (Γ N : Set G)) hΓopen
    (fun x _ => by
      obtain ⟨N, hN⟩ := exists_mem_compactCovering x
      exact mem_iUnion.2 ⟨N, hCΓ N (subset_union_right hN)⟩) hdir
  have hΓ'M : Γ' ≤ Γ M := by
    rw [← hU'cl]
    exact (Subgroup.closure_le _).2 hM
  obtain ⟨W, hW, hWk⟩ := Aux_CF.pair_nss hs'.1 hπ'
  obtain ⟨N, hN⟩ := hsmall W hW
  refine ⟨max M N, hΓ'M.trans (hΓmono (le_max_left _ _)), ?_⟩
  exact hWk _ (fun x hx => hN (hanti (by omega : N ≤ max M N + N₀) hx))
