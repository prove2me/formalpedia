-- Prove2me | solution 1 for GroundTheory.ProfCoh.scdp_le_cdp_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:57.975242+00:00
-- url     : https://prove2.me/submissions/33ef96f7-73d8-4450-b240-537b0ba4095b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_nsmul_id_apply
import Theorems.Thm_GroundTheory_ProfCoh_subQuotShortComplex_shortExact
import Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_eq_bot_iff
import Theorems.Thm_GroundTheory_ProfCoh_eq_zero_of_pow_nsmul_eq_zero
import Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_cdp_le
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_comp
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_scdp_le_iff
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__fb61531df879
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (hp : p.Prime) : scdp p G ≤ cdp p G + 1 := by
  by_cases htop : cdp p G = ⊤
  · rw [htop]
    simp
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hcd : cdp p G ≤ n := hn ▸ le_rfl
  rw [← hn, scdp_le_iff]
  intro A _ q hq
  have hq' : n + 1 < q := by exact_mod_cast hq
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let φ : A →ₗ[ULift.{u} ℤ] A := p • LinearMap.id
  have hφ : ∀ g (a : A), φ (A.ρ g a) = A.ρ g (φ a) := fun g a => by simp [φ, map_nsmul]
  let K := LinearMap.ker φ
  let I := LinearMap.range φ
  have hK : ∀ g, K ≤ K.comap (A.ρ g) := by
    intro g a ha
    simp only [K, LinearMap.mem_ker, Submodule.mem_comap] at ha ⊢
    rw [hφ, ha, map_zero]
  have hI : ∀ g, I ≤ I.comap (A.ρ g) := by
    rintro g _ ⟨b, rfl⟩
    exact ⟨A.ρ g b, hφ g b⟩
  let π : A ⟶ A.subrepresentation I hI :=
    Rep.ofHom ⟨φ.rangeRestrict, fun g => LinearMap.ext fun a => Subtype.ext (hφ g a)⟩
  let S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) :=
    ShortComplex.mk (Rep.subtype A K hK) π (by
      ext w
      exact LinearMap.mem_ker.1 w.2)
  have : IsDiscreteRep S.X₁ := isDiscreteRep_subrepresentation A K hK
  have : IsDiscreteRep S.X₂ := (inferInstance : IsDiscreteRep A)
  have : IsDiscreteRep S.X₃ := isDiscreteRep_subrepresentation A I hI
  have hS : S.ShortExact :=
    { exact := by
        rw [← ShortComplex.exact_map_iff_of_faithful _
          (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ))),
          ShortComplex.moduleCat_exact_iff]
        intro a ha
        exact ⟨⟨a, LinearMap.mem_ker.2 (congrArg Subtype.val ha)⟩, rfl⟩
      mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
      epi_g := (Rep.epi_iff_surjective _).2 (LinearMap.surjective_rangeRestrict φ) }
  have hKp : ∀ x : A.subrepresentation K hK, p • x = 0 := fun x =>
    Subtype.ext (LinearMap.mem_ker.1 x.2)
  have hQp : ∀ x : A.quotient I hI, p • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I x
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, rfl⟩
  have hKq := subsingleton_cohomology_of_cdp_le hp hcd _ hKp (show n < q' + 1 by omega)
  have hQq := subsingleton_cohomology_of_cdp_le hp hcd _ hQp (show n < q' by omega)
  have hπinj : ∀ y : cohomology A (q' + 1), (cohomologyMap π (q' + 1)).hom y = 0 → y = 0 := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (q' + 1)) y hy
    rw [← hz, @Subsingleton.elim _ hKq z 0]
    exact map_zero _
  have hιinj : ∀ y : cohomology (A.subrepresentation I hI) (q' + 1),
      (cohomologyMap (Rep.subtype A I hI) (q' + 1)).hom y = 0 → y = 0 := by
    intro y hy
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (cohomology_exact₁ (subQuotShortComplex_shortExact A I hI) q' (q' + 1) rfl) y hy
    rw [← hw, @Subsingleton.elim _ hQq w 0]
    exact map_zero _
  have hcomp : π ≫ Rep.subtype A I hI = p • 𝟙 A := by
    ext a
    rfl
  have hpinj : ∀ x : cohomology A (q' + 1), p • x = 0 → x = 0 := by
    intro x hx
    rw [← cohomologyMap_nsmul_id_apply, ← hcomp, cohomologyMap_comp] at hx
    exact hπinj x (hιinj _ hx)
  rw [primaryComponent_eq_bot_iff]
  rintro x ⟨k, hk⟩
  exact eq_zero_of_pow_nsmul_eq_zero hpinj k x hk
end GroundTheory.ProfCoh
