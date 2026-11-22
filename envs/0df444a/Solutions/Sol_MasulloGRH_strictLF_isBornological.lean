-- Prove2me | solution 1 for MasulloGRH.strictLF_isBornological
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T10:23:25.532969+00:00
-- url     : https://prove2.me/submissions/b16e3e52-ffba-4486-bc99-c5e492a453bf

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Topology Filter Uniformity Pointwise

namespace BarAux

universe u

lemma lc_tvs {E : Type u} [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (h : IsLocallyConvexTopology E t) : IsTopologicalAddGroup E ∧ ContinuousSMul ℂ E := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact ⟨hp.topologicalAddGroup, hp.continuousSMul⟩

lemma frechet_baire {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : IsFrechet E) : BaireSpace E := by
  obtain ⟨hlc, ⟨hT2, hc⟩, hm⟩ := h
  obtain ⟨h1, h2⟩ := lc_tvs hlc
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine ⟨fun {f} hf => ?_⟩
    apply hc f
    refine ⟨hf.1, fun U hU => ?_⟩
    have hs : {p : E × E | p.2 - p.1 ∈ U} ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero']
      exact ⟨U, hU, fun p hp => by simpa [sub_eq_add_neg] using hp⟩
    obtain ⟨A, hA, hAA⟩ := mem_prod_same_iff.1 (hf.2 hs)
    exact ⟨A, hA, fun x hx y hy => hAA (Set.mk_mem_prod hy hx)⟩
  infer_instance

/-- the topology of a single seminorm -/
noncomputable def sTop {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    TopologicalSpace E :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) (fun _ : PUnit.{u+1} => p)).topology

lemma sTop_ws {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    @WithSeminorms ℂ E PUnit.{u+1} _ _ _ (fun _ => p) (sTop p) := by
  letI := sTop p
  exact ⟨rfl⟩

lemma sTop_lc {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    IsLocallyConvexTopology E (sTop p) := ⟨PUnit, inferInstance, _, sTop_ws p⟩

lemma sTop_cont_into {E : Type u} [AddCommGroup E] [Module ℂ E] {F : Type*} [AddCommGroup F]
    [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] (f : F →ₗ[ℂ] E)
    (p : Seminorm ℂ E) (hf : Continuous (p.comp f)) : @Continuous F E _ (sTop p) f := by
  letI := sTop p
  exact WithSeminorms.continuous_of_continuous_comp (sTop_ws p) f (fun _ => hf)

lemma sTop_cont {E : Type u} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    @Continuous E ℝ (sTop p) _ p := by
  letI := sTop p
  exact WithSeminorms.continuous_seminorm (sTop_ws p) PUnit.unit


lemma bdd_image_val {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (X : Submodule ℂ E) {B : Set X} (hB : Bornology.IsVonNBounded ℂ B) :
    Bornology.IsVonNBounded ℂ (Subtype.val '' B) := by
  intro U hU
  have h0 : ((0 : X) : E) = 0 := rfl
  have hU' : Subtype.val ⁻¹' U ∈ 𝓝 (0 : X) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (h0 ▸ hU)
  have := hB hU'
  filter_upwards [this] with a ha
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_smul_set.1 (ha hx)
  refine Set.mem_smul_set.2 ⟨(y : E), hy, ?_⟩
  rw [← hxy]
  rfl

lemma metr_born {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [FirstCountableTopology X]
    (p : Seminorm ℂ X) (hp : ∀ B : Set X, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) :
    Continuous p := by
  by_contra hc
  have hball : p.closedBall 0 1 ∉ 𝓝 (0 : X) := fun h => hc (Seminorm.continuous' h)
  obtain ⟨V, hV⟩ := (𝓝 (0 : X)).exists_antitone_basis
  have hcast : ∀ k : ℕ, ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := fun k => by push_cast; ring
  have hne : ∀ k : ℕ, ((k : ℂ) + 1) ≠ 0 := fun k => by
    rw [hcast]; exact_mod_cast Nat.succ_ne_zero k
  have hz : ∀ k : ℕ, ∃ z, z ∈ ((k : ℂ) + 1)⁻¹ • V k ∧ 1 < p z := by
    intro k
    by_contra h
    push_neg at h
    apply hball
    refine Filter.mem_of_superset ((set_smul_mem_nhds_zero_iff (inv_ne_zero (hne k))).2
      (hV.mem k)) ?_
    intro z hz
    simpa [Seminorm.mem_closedBall, sub_zero] using h z hz
  choose z hzV hzp using hz
  let y : ℕ → X := fun k => ((k : ℂ) + 1) • z k
  have hyV : ∀ k, y k ∈ V k := by
    intro k
    obtain ⟨v, hv, hvz⟩ := Set.mem_smul_set.1 (hzV k)
    have : y k = v := by
      simp only [y, ← hvz, smul_smul, mul_inv_cancel₀ (hne k), one_smul]
    rw [this]; exact hv
  have ht := hV.tendsto hyV
  obtain ⟨M, hM⟩ := hp _ (ht.isVonNBounded_range ℂ)
  obtain ⟨k, hk⟩ := exists_nat_gt M
  have h1 : p (y k) ≤ M := hM ⟨y k, ⟨k, rfl⟩, rfl⟩
  have h2 : p (y k) = ((k : ℝ) + 1) * p (z k) := by
    simp only [y, map_smul_eq_mul, hcast, Complex.norm_natCast]
    push_cast; ring
  have h3 := hzp k
  have h4 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

end BarAux

open BarAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsStrictLF E) : IsBornological E := by
  obtain ⟨X, hmono, hexh, hX, htop⟩ := hE
  intro p hp
  have hmem : sTop p ∈ {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val} := by
    refine ⟨sTop_lc p, fun n => ?_⟩
    obtain ⟨h1, h2⟩ := lc_tvs (hX n).1
    haveI := (hX n).2.2
    have hpn : Continuous (p.comp (X n).subtype) := by
      apply metr_born
      intro B hB
      obtain ⟨M, hM⟩ := hp _ (bdd_image_val (X n) hB)
      refine ⟨M, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hM ⟨(x : E), ⟨x, hx, rfl⟩, rfl⟩
    exact sTop_cont_into ((X n).subtype) p hpn
  have hle : ‹TopologicalSpace E› ≤ sTop p := htop ▸ sInf_le hmem
  exact @Continuous.comp _ _ _ _ (sTop p) _ _ _ (sTop_cont p) (continuous_id_of_le hle)
