-- Prove2me | solution 3 for MasulloGRH.strictLF_limit_subspace_of_bornological
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:52:22.27145+00:00
-- url     : https://prove2.me/submissions/3f53ad72-3725-4f6d-86bd-368ed9963653

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages

set_option autoImplicit false

open MasulloGRH Topology Filter

namespace LimitSubspaceAux

/-- A continuous seminorm is bounded on every von Neumann bounded set. -/
lemma seminorm_bddAbove_of_continuous {M : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] (q : Seminorm ℂ M) (hq : Continuous q) (S : Set M)
    (hS : Bornology.IsVonNBounded ℂ S) : BddAbove (q '' S) := by
  have hU : {x : M | q x < 1} ∈ 𝓝 (0 : M) :=
    (isOpen_lt hq continuous_const).mem_nhds (by simp)
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (hS hU)
  set c : ℂ := ((max r 1 : ℝ) : ℂ) with hc_def
  have hcn : ‖c‖ = max r 1 := by
    rw [hc_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hc : r ≤ ‖c‖ := by rw [hcn]; exact le_max_left _ _
  refine ⟨‖c‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp (hr c hc hx)
  rw [map_smul_eq_mul]
  have hu' : q u < 1 := hu
  have := apply_nonneg q u
  nlinarith [norm_nonneg c]

/-- Boundedness passes from a submodule (subspace topology) to the ambient space. -/
lemma image_val_bounded {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : Submodule ℂ E) (B : Set W) (hB : Bornology.IsVonNBounded ℂ B) :
    Bornology.IsVonNBounded ℂ ((↑) '' B : Set E) := by
  intro U hU
  have hU' : ((↑) : W → E) ⁻¹' U ∈ 𝓝 (0 : W) := by
    rw [nhds_subtype_eq_comap]
    exact Filter.preimage_mem_comap (by simpa using hU)
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (hB hU')
  refine absorbs_iff_norm.mpr ⟨r, fun c hc => ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp (hr c hc hx)
  exact Set.mem_smul_set.mpr ⟨(u : E), hu, by simp⟩

/-- Boundedness passes from the ambient space to a submodule (subspace topology). -/
lemma bounded_of_image_val {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : Submodule ℂ E) (B : Set W) (hB : Bornology.IsVonNBounded ℂ ((↑) '' B : Set E)) :
    Bornology.IsVonNBounded ℂ B := by
  intro U hU
  rw [nhds_subtype_eq_comap] at hU
  obtain ⟨U', hU', hsub⟩ := hU
  have hU'0 : U' ∈ 𝓝 (0 : E) := by simpa using hU'
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (hB hU'0)
  refine absorbs_iff_norm.mpr ⟨max r 1, fun c hc => ?_⟩
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith [le_max_right r 1]
  intro x hx
  have hmem := hr c (le_trans (le_max_left _ _) hc) ⟨x, hx, rfl⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc0] at hmem ⊢
  apply hsub
  simpa using hmem

end LimitSubspaceAux

open LimitSubspaceAux in
theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hborn : IsBornological V) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} := by
  obtain ⟨hHLCS, hbdd⟩ :=
    bounded_in_strict_frechet_stages E X hmono hexh (fun n => (hX n).1) htop
  obtain ⟨⟨ι, hne, p, hp⟩, _hT2⟩ := hHLCS
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  apply le_antisymm
  · apply le_sInf
    rintro t ⟨⟨ι', hne', q, hq⟩, hcont⟩
    rw [← continuous_id_iff_le]
    have hqi : ∀ i, @Continuous V ℝ instTopologicalSpaceSubtype _ (q i : V → ℝ) := by
      intro i
      apply hborn
      intro B hB
      obtain ⟨n, A, _hA, hBA⟩ := hbdd _ (image_val_bounded V B hB)
      -- every point of `B` lies in the step `X n`
      have hBX : ∀ z ∈ B, (z : E) ∈ X n := by
        intro z hz
        have : (z : E) ∈ ((↑) '' B : Set E) := ⟨z, hz, rfl⟩
        rw [hBA] at this
        obtain ⟨a, _, ha⟩ := this
        rw [← ha]; exact a.2
      set B' : Set ↥(V ⊓ X n) := (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)) ⁻¹' B
        with hB'_def
      have himg : ((↑) '' B' : Set E) = ((↑) '' B : Set E) := by
        ext y; constructor
        · rintro ⟨z, hz, rfl⟩; exact ⟨_, hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          refine ⟨⟨(z : E), z.2, hBX z hz⟩, ?_, rfl⟩
          have he : Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)
              (⟨(z : E), z.2, hBX z hz⟩ : ↥(V ⊓ X n)) = z := Subtype.ext rfl
          rw [hB'_def, Set.mem_preimage, he]; exact hz
      have hB'b : Bornology.IsVonNBounded ℂ B' :=
        bounded_of_image_val (V ⊓ X n) B' (by rw [himg]; exact image_val_bounded V B hB)
      have hqc : Continuous ((q i).comp (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V))) :=
        (hq.continuous_seminorm i).comp (hcont n)
      obtain ⟨M, hM⟩ := seminorm_bddAbove_of_continuous _ hqc B' hB'b
      refine ⟨M, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have he : Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)
          (⟨(z : E), z.2, hBX z hz⟩ : ↥(V ⊓ X n)) = z := Subtype.ext rfl
      have hz' : (⟨(z : E), z.2, hBX z hz⟩ : ↥(V ⊓ X n)) ∈ B' := by
        rw [hB'_def, Set.mem_preimage, he]; exact hz
      have := hM ⟨_, hz', rfl⟩
      simpa [he] using this
    exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ V V ι' _ _ _ _ _ _ (RingHom.id ℂ) _ q
      instTopologicalSpaceSubtype inferInstance t hq LinearMap.id (fun i => hqi i)
  · apply sInf_le
    refine ⟨⟨ι, hne, p.comp V.subtype, ?_⟩, fun n => ?_⟩
    · exact LinearMap.withSeminorms_induced hp V.subtype
    · exact continuous_induced_rng.2 continuous_subtype_val
