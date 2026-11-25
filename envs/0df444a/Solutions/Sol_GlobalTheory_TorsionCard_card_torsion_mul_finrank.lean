-- Prove2me | solution 1 for GlobalTheory.TorsionCard.card_torsion_mul_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:59.922837+00:00
-- url     : https://prove2.me/submissions/e4c8d9b9-f939-4ed3-bf4c-1ba0e9a96b99

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
import Theorems.Thm_GlobalTheory_TorsionCard_red_val
import Theorems.Thm_GlobalTheory_TorsionCard_exists_lift
import Theorems.Thm_GlobalTheory_TorsionCard_card_torsion
import Theorems.Thm_GlobalTheory_TorsionCard_exists_chi
import Theorems.Thm_GlobalTheory_TorsionCard_finrank_eq_relIndex
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_fix_iff
import Theorems.Thm_GlobalTheory_Cyc_mem_fixingSubgroup_adjoin_iff
import Theorems.Thm_GlobalTheory_UnramCyc_chi_onto_of_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory GlobalTheory.TorsionCard
variable {l : ℕ} [hl : Fact l.Prime]
set_option maxHeartbeats 800000
namespace GlobalTheory.TorsionCard
theorem _root_.solution : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), l ≠ 2 → K.1 ≤ Ks K 1 → W.DelF.card * Module.finrank ↥(K0 K) ↥K.1 = l - 1 := by
  intro l _ P K LL n W h2 hK
  classical
  obtain ⟨χ, hχ⟩ := exists_chi P
  have hle : K0 K ≤ K.1 := inf_le_left
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  have hval : ∀ g : ↥(GK K), ((χK g : ℤ_[l]) : ℚ_[l]) = ((P.PD K).χ g : ℚ_[l]) := by
    intro g
    rw [P.PD_χ K g]
    exact hχ g
  have hO : Function.Injective (algebraMap (OL LL) LL.1) := Subtype.val_injective
  have hkey : ∀ g : ↥(GK K), W.resΓ g = 1 ↔ χK g = 1 := by
    intro g
    have hr := W.χΓ_res g
    constructor
    · intro h
      rw [h, map_one, Units.val_one, map_one] at hr
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 :=
        (algebraMap ℚ_[l] LL.1).injective (by rw [← hr, map_one])
      apply Units.ext
      apply PadicInt.ext
      rw [hval, h1]
      simp
    · intro h
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
        rw [← hval, h]
        simp
      rw [h1, map_one] at hr
      have h3 : ((W.χΓ (W.resΓ g) : (OL LL)ˣ) : OL LL) = 1 := hO (by rw [hr, map_one])
      apply W.χΓ_inj
      rw [map_one]
      exact Units.ext h3
  let ψ : W.Gam →* ℤ_[l]ˣ :=
    W.resΓ.liftOfRightInverse (Function.surjInv W.resΓ_onto)
      (Function.rightInverse_surjInv W.resΓ_onto)
      ⟨χK, fun g hg => MonoidHom.mem_ker.mpr ((hkey g).mp (MonoidHom.mem_ker.mp hg))⟩
  have hψ : ∀ g : ↥(GK K), ψ (W.resΓ g) = χK g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun γ hγ => ?_
    obtain ⟨g, rfl⟩ := W.resΓ_onto γ
    rw [hψ] at hγ
    exact (hkey g).mpr hγ
  have hfix : ∀ g : GQ l, g ∈ (K0 K).fixingSubgroup → red l (χ g) = 1 → g ∈ GK K := by
    intro g hg hr
    have hz : PadicInt.toZMod ((χ g : ℤ_[l]) - 1) = 0 := by
      rw [map_sub, ← red_val, hr, Units.val_one, map_one, sub_self]
    have hd : (l : ℤ_[l]) ^ 1 ∣ (χ g : ℤ_[l]) - 1 := by
      rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hz
    have hnorm : ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [← hχ g]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (Ideal.mem_span_singleton.mpr hd)
      simpa [PadicInt.norm_def] using this
    have hζ := (GlobalTheory.Cyc.IsCyc.fix_iff P.χQ_cyc g 1).mpr hnorm
    have hadj : g ∈ (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ 1 = 1}).fixingSubgroup :=
      (GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff _ g).mpr fun x hx => hζ x hx
    have hKs : g ∈ (Ks K 1).fixingSubgroup := by
      unfold Ks
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hg, hadj⟩
    exact IntermediateField.fixingSubgroup_le hK hKs
  have hfd0 : FiniteDimensional ℚ_[l] (K0 K) := by
    have : FiniteDimensional ℚ_[l] K.1 := K.2
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  let K0' : FinExt l := ⟨K0 K, hfd0⟩
  have honto : ∀ c : ℤ_[l]ˣ, ∃ g ∈ (K0 K).fixingSubgroup, χ g = c := by
    intro c
    obtain ⟨g, hg, hgc⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K0' inf_le_right c
    exact ⟨g, hg, Units.ext (PadicInt.ext (by rw [hχ g, hgc]))⟩
  have hk : ∀ x : ℤ_[l]ˣ, red l x = 1 → x ∈ ψ.range := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := honto x
    exact ⟨W.resΓ ⟨g, hfix g hg hx⟩, by rw [hψ]; rfl⟩
  have hct := card_torsion h2 ψ hψinj hk
  have hdel : W.DelF.card = Nat.card {γ : W.Gam // IsOfFinOrder γ} := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun γ => by
      rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one])
  let G0 := (K0 K).fixingSubgroup
  let F : ↥G0 →* (ZMod l)ˣ := (red l).comp (χ.comp G0.subtype)
  have hF : Function.Surjective F := by
    intro u
    obtain ⟨x, -, hxu⟩ := exists_lift h2 u
    obtain ⟨g, hg, hgx⟩ := honto x
    exact ⟨⟨g, hg⟩, by simp [F, hgx, hxu]⟩
  let H0 := (GK K).subgroupOf G0
  have hkerF : F.ker ≤ H0 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    exact Subgroup.mem_subgroupOf.mpr (hfix g g.2 hg)
  have hidx : H0.index = (H0.map F).index := by
    rw [← Subgroup.index_comap_of_surjective _ hF, Subgroup.comap_map_eq_self hkerF]
  have hmap : H0.map F = ((red l).comp ψ).range := by
    ext u
    constructor
    · rintro ⟨g0, hg0, rfl⟩
      refine ⟨W.resΓ ⟨g0, Subgroup.mem_subgroupOf.mp hg0⟩, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
    · rintro ⟨γ, rfl⟩
      obtain ⟨g, rfl⟩ := W.resΓ_onto γ
      refine ⟨⟨g, IntermediateField.fixingSubgroup_le hle g.2⟩, Subgroup.mem_subgroupOf.mpr g.2, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
  have hcard := Subgroup.card_mul_index (H0.map F)
  rw [Nat.card_eq_fintype_card (α := (ZMod l)ˣ), ZMod.card_units] at hcard
  rw [finrank_eq_relIndex, hdel, hct, ← hmap]
  change _ * H0.index = _
  rw [hidx]
  exact hcard
end GlobalTheory.TorsionCard
