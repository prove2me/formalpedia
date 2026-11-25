-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.exists_proj_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:59.691691+00:00
-- url     : https://prove2.me/submissions/f75c858b-8a65-4eaf-ba5a-dcfb9eb6f79d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_norm_le
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_det_one_sub_le
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_aniso
import Theorems.Thm_GlobalTheory_DegCnt_FixDisc_mem_fixSp
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution {H : HermSpace K V} (hK : IsCMUnram K) (hP : PD H.B.flip) {η : V ≃ₗ[K] V}
    (hη : ∀ x y, H.B (η x) (η y) = H.B x y) {g : ℕ} (hg : 0 < g) :
    ∃ (p : V →ₗ[K] fixSp η) (F : V ≃ₗ[K] V), (∀ t : fixSp η, p t = t) ∧
      (∀ (x : V) (t : fixSp η), H.B t (p x) = H.B t x) ∧ (∀ x, p (x - η x) = 0) ∧
      (∀ x, F x = p x + (g : K)⁻¹ • (x - η x)) ∧
      ((|Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| : ℚ) : ℝ) ≤
        (2 / (g : ℝ)) ^ (2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K) := by
  set S : Submodule K V := LinearMap.range ((η : V →ₗ[K] V) - LinearMap.id) with hS
  have hrk : Module.finrank K S + Module.finrank K (fixSp η) = Module.finrank K V :=
    LinearMap.finrank_range_add_finrank_ker _
  have horth : ∀ t ∈ fixSp η, ∀ s ∈ S, H.B t s = 0 := by
    rintro t ht _ ⟨y, rfl⟩
    have := hη t y
    rw [(mem_fixSp η t).1 ht] at this
    simp [this]
  have hdis : Disjoint (fixSp η) S := by
    rw [Submodule.disjoint_def]
    exact fun x h1 h2 => aniso hP x (horth x h1 x h2)
  have hc : IsCompl (fixSp η) S :=
    ⟨hdis, codisjoint_iff.2 (Submodule.eq_top_of_disjoint _ _ (by omega) hdis)⟩
  set p := Submodule.projectionOnto (fixSp η) S hc with hp
  have p1 : ∀ t : fixSp η, p t = t := Submodule.projectionOnto_apply_left hc
  have p2 : ∀ x, p x = 0 ↔ x ∈ S := fun x => Submodule.projectionOnto_apply_eq_zero_iff hc
  have p3 : ∀ x, x - p x ∈ S := fun x => by rw [← p2, map_sub, p1, sub_self]
  have p4 : ∀ x, x - η x ∈ S := fun x => ⟨-x, by simp; abel⟩
  have hg0 : (g : K) ≠ 0 := by exact_mod_cast hg.ne'
  set F₀ : V →ₗ[K] V := (fixSp η).subtype ∘ₗ p + (g : K)⁻¹ • (LinearMap.id - (η : V →ₗ[K] V)) with hF₀
  have f1 : ∀ x, F₀ x = p x + (g : K)⁻¹ • (x - η x) := fun x => rfl
  have hinj : Function.Injective F₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have a1 := congrArg p hx
    rw [f1, map_add, map_smul, (p2 _).2 (p4 x), p1, smul_zero, add_zero, map_zero] at a1
    rw [f1, a1, Submodule.coe_zero, zero_add, smul_eq_zero, sub_eq_zero] at hx
    have a2 : x ∈ fixSp η := (mem_fixSp η x).2 (hx.resolve_left (inv_ne_zero hg0)).symm
    have a3 := p1 ⟨x, a2⟩
    rw [a1] at a3
    exact (congrArg Subtype.val a3).symm
  refine ⟨p, LinearEquiv.ofInjectiveEndo F₀ hinj, p1, fun x t => ?_, fun x => (p2 _).2 (p4 x), f1, ?_⟩
  · have := horth t t.2 _ (p3 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hFF : ((LinearEquiv.ofInjectiveEndo F₀ hinj : V ≃ₗ[K] V) : V →ₗ[K] V) = F₀ := rfl
  have hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hex : 2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K =
      Module.finrank K S * Module.finrank ℚ K := by
    rw [hd, ← hrk, Nat.add_sub_cancel]; ring
  rw [hFF, hex, pow_mul]
  refine norm_le _ _ fun σ => ?_
  have hηS : ∀ x ∈ S, (η : V →ₗ[K] V) x ∈ S := fun x hx => by
    have := S.sub_mem hx (p4 x)
    simpa using this
  have hFS : S ≤ S.comap F₀ := fun x hx => by
    rw [Submodule.mem_comap, f1, (p2 x).2 hx, Submodule.coe_zero, zero_add]
    exact S.smul_mem _ (p4 x)
  have q1 : S.mapQ S F₀ hFS = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
    rw [Submodule.Quotient.eq, f1]
    have := S.sub_mem (S.smul_mem (g : K)⁻¹ (p4 x)) (p3 x)
    convert this using 1
    abel
  have q2 : F₀.restrict hFS = (g : K)⁻¹ • (LinearMap.id - (η : V →ₗ[K] V).restrict hηS) := by
    ext x
    change F₀ x = (g : K)⁻¹ • ((x : V) - η x)
    rw [f1, (p2 x).2 x.2, Submodule.coe_zero, zero_add]
  have hb := det_one_sub_le σ (H.B.domRestrict₁₂ S S) ((η : V →ₗ[K] V).restrict hηS) (hK.2.1 σ)
    (fun x y => H.herm x y) (fun w hw => hP σ w (fun h0 => hw (Subtype.ext h0))) (fun x y => hη x y)
  rw [LinearMap.det_eq_det_mul_det S F₀ hFS, q1, q2, LinearMap.det_id, mul_one, LinearMap.det_smul, map_mul,
    norm_mul, map_pow, norm_pow, map_inv₀, norm_inv, map_natCast, Complex.norm_natCast, div_eq_inv_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left hb (by positivity)
end GlobalTheory.DegCnt.FixDisc
