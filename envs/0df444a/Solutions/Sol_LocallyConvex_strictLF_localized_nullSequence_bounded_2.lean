-- Prove2me | solution 2 for LocallyConvex.strictLF_localized_nullSequence_bounded
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T00:38:00.393391+00:00
-- url     : https://prove2.me/submissions/4af4ceb5-afb7-4d88-884b-ce920aa272e3

import Theorems.Thm_LocallyConvex_frechet_closedDisk_image_absorption
import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_strictLF_quotient_t2Space

set_option autoImplicit false
open MasulloGRH Topology Filter

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hloc : ∀ n : ℕ, ∃ U ∈ nhds (0 : X n), ∃ j : ℕ,
      closure ((fun x : X n => V.mkQ (x : E)) '' U) ⊆
        Set.range (Submodule.mapQ (V.comap (X j).subtype) V (X j).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n),
      ∀ k : ℕ, m ≤ k → ∀ y : ℕ → X k,
        Filter.Tendsto y Filter.atTop (nhds (0 : X k)) →
        (∀ i, ∃ x ∈ U, ((x : E) - (y i : E)) ∈ V) →
        ∀ W ∈ nhds (0 : X m), ∃ R : ℝ, 0 < R ∧
          ∀ r : ℝ, R ≤ r → ∀ i, ∃ w ∈ W,
            ((y i : E) - (r : ℂ) • (w : E)) ∈ V := by
  classical
  letI : Module ℝ E := Module.restrictScalars ℝ ℂ E
  obtain ⟨ι, hι, p, hp⟩ :=
    (strictLF_hlcs_and_closed_steps E X hmono hexh hX htop).1.1
  letI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hp.continuousSMul
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  letI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  letI : T2Space (E ⧸ V) := strictLF_quotient_t2Space E X hmono hexh hX htop V hV
  letI : ContinuousSMul ℝ (E ⧸ V) := IsScalarTower.continuousSMul ℂ
  intro n
  obtain ⟨ιn, hιn, pn, hpn⟩ := (hX n).1
  letI : LocallyConvexSpace ℝ (X n) := hpn.toLocallyConvexSpace
  letI : ContinuousSMul ℝ (X n) := IsScalarTower.continuousSMul ℂ
  obtain ⟨U₀, hU₀, j, hj⟩ := hloc n
  obtain ⟨U, ⟨hU, hUdisk⟩, hUU⟩ := (nhds_hasBasis_absConvex ℝ (X n)).mem_iff.mp hU₀
  let qn : X n →L[ℂ] E ⧸ V := V.mkQL.comp (X n).subtypeL
  let C : Set (E ⧸ V) := closure (qn '' U)
  have hCimage : C ⊆ Set.range (V.mkQL.comp (X (max n j)).subtypeL) := by
    intro z hz
    have hzj := hj (closure_mono (Set.image_mono hUU) hz)
    obtain ⟨zj, hzj⟩ := hzj
    obtain ⟨xj, rfl⟩ := Submodule.Quotient.mk_surjective (V.comap (X j).subtype) zj
    refine ⟨⟨(xj : E), hmono (le_max_right n j) xj.property⟩, ?_⟩
    exact hzj
  have hCclosed : IsClosed C := isClosed_closure
  have hCdisk : AbsConvex ℝ C := by
    apply AbsConvex.closure
    let qnr : X n →ₗ[ℝ] E ⧸ V := qn.toLinearMap.restrictScalars ℝ
    refine ⟨?_, hUdisk.2.linear_image qnr⟩
    intro r hr z hz
    obtain ⟨v, ⟨x, hx, rfl⟩, rfl⟩ := hz
    exact ⟨r • x, hUdisk.1.smul_mem hr hx, qnr.map_smul r x⟩
  refine ⟨max n j, le_max_left n j, U, hU, ?_⟩
  intro k hmk y hy hyU W hW
  let a : X k →L[ℂ] E ⧸ V := V.mkQL.comp (X k).subtypeL
  let b : X (max n j) →L[ℂ] E ⧸ V := V.mkQL.comp (X (max n j)).subtypeL
  have hyC : a '' Set.range y ⊆ C := by
    rintro z ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hyU i
    apply subset_closure
    exact ⟨x, hx, (Submodule.Quotient.eq V).mpr hxy⟩
  obtain ⟨R, hR, hbound⟩ := LocallyConvex.frechet_closedDisk_image_absorption
    (X k) (X (max n j)) (E ⧸ V) (hX k) (hX (max n j))
    a b C hCclosed hCdisk hCimage (Set.range y) (hy.isVonNBounded_range ℂ) hyC W hW
  refine ⟨R, hR, ?_⟩
  intro r hr i
  obtain ⟨w, hw, heq⟩ := hbound r hr (y i) ⟨i, rfl⟩
  refine ⟨w, hw, (Submodule.Quotient.eq V).mp ?_⟩
  simpa only [a, b, ContinuousLinearMap.comp_apply, Submodule.mkQL_apply,
    Submodule.subtypeL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_smul] using heq
