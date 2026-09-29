-- Prove2me | solution 1 for LocalNewvector.AdelicSpan.exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c5708e8a-22cb-5424-886f-b763cb6949b4

import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Mathlib.NumberTheory.Padics.RingHoms
import Theorems.Thm_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
import Theorems.Thm_LocalNewvector_exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
import Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
import Theorems.Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace TwistNewvec

variable (q : ℕ) [Fact q.Prime]

abbrev unitsCoe : ℤ_[q]ˣ →* ℚ_[q]ˣ := Units.map PadicInt.Coe.ringHom.toMonoidHom

@[scoped simp] theorem val_unitsCoe (u : ℤ_[q]ˣ) : ((unitsCoe q u : ℚ_[q]ˣ) : ℚ_[q]) = ((u : ℤ_[q]) : ℚ_[q]) := rfl

theorem norm_unitsCoe (u : ℤ_[q]ˣ) : ‖((unitsCoe q u : ℚ_[q]ˣ) : ℚ_[q])‖ = 1 := by
  rw [val_unitsCoe]
  exact PadicInt.isUnit_iff.mp u.isUnit

theorem unitsCoe_mkUnits {z : ℚ_[q]ˣ} (hz : ‖(z : ℚ_[q])‖ = 1) :
    unitsCoe q (PadicInt.mkUnits hz) = z :=
  Units.ext (by rw [val_unitsCoe, PadicInt.mkUnits_eq])

theorem norm_eq_one_of_norm_sub_one_lt {z : ℚ_[q]} (hz : ‖z - 1‖ < 1) : ‖z‖ = 1 := by
  have h1 : ‖(1 : ℚ_[q])‖ = 1 := norm_one
  have hne : ‖z - 1‖ ≠ ‖(1 : ℚ_[q])‖ := by rw [h1]; exact hz.ne
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel, h1, max_eq_right hz.le] at this
  exact this

theorem zpow_neg_le_zpow_neg {m n : ℕ} (h : m ≤ n) : (q : ℝ) ^ (-(n : ℤ)) ≤ (q : ℝ) ^ (-(m : ℤ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
  exact zpow_le_zpow_right₀ hq1 (by omega)

theorem zpow_neg_lt_one {n : ℕ} (hn : 1 ≤ n) : (q : ℝ) ^ (-(n : ℤ)) < 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  calc (q : ℝ) ^ (-(n : ℤ)) ≤ (q : ℝ) ^ (-(1 : ℤ)) := zpow_le_zpow_right₀ hq1.le (by omega)
    _ < 1 := by rw [zpow_neg, zpow_one, inv_lt_one_iff₀]; exact Or.inr hq1

theorem unitsMap_toZModPow_eq_one {b : ℕ} (u : ℤ_[q]ˣ)
    (h : ‖((u : ℤ_[q]) : ℚ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(b : ℤ))) :
    Units.map (PadicInt.toZModPow b).toMonoidHom u = 1 := by
  apply Units.ext
  rw [Units.coe_map, Units.val_one]
  show PadicInt.toZModPow b (u : ℤ_[q]) = 1
  have hmem : (u : ℤ_[q]) - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ b} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    have : ‖((u : ℤ_[q]) - 1 : ℤ_[q])‖ = ‖((u : ℤ_[q]) : ℚ_[q]) - 1‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    rw [this]; exact h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

def unitsToIdele : ℚ_[q]ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)).comp
    ((AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).comp
      (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom))

theorem unitsToIdele_apply (z : ℚ_[q]ˣ) :
    unitsToIdele q z =
      Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
        (AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom z)) := rfl

def etaLoc (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) : ℚ_[q]ˣ →* ℂˣ := η.comp (unitsToIdele q)

def EtaUnits (q : ℕ) [Fact q.Prime] (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[q]ˣ,
    η (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
        (AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u))))
      = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹

theorem etaLoc_unitsCoe {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} {η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hηu : EtaUnits q b χ₀ η) (u : ℤ_[q]ˣ) :
    etaLoc q η (unitsCoe q u) = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹ :=
  hηu u

theorem etaLoc_eq_one_of_norm_sub_one_le {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} {η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hηu : EtaUnits q b χ₀ η) {B : ℕ} (hbB : b ≤ B) (h1B : 1 ≤ B)
    (z : ℚ_[q]ˣ) (hz : ‖(z : ℚ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(B : ℤ))) : etaLoc q η z = 1 := by
  have hz1 : ‖(z : ℚ_[q])‖ = 1 :=
    norm_eq_one_of_norm_sub_one_lt q (lt_of_le_of_lt hz (zpow_neg_lt_one q h1B))
  have hu : unitsCoe q (PadicInt.mkUnits hz1) = z := unitsCoe_mkUnits q hz1
  rw [← hu, etaLoc_unitsCoe q hηu]
  have hred : Units.map (PadicInt.toZModPow b).toMonoidHom (PadicInt.mkUnits hz1) = 1 := by
    refine unitsMap_toZModPow_eq_one q _ ?_
    rw [PadicInt.mkUnits_eq]
    exact hz.trans (zpow_neg_le_zpow_neg q hbB)
  rw [hred, map_one, inv_one]

theorem etaLoc_eq_one_of_mem_higherUnits {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} {η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hηu : EtaUnits q b χ₀ η) (z : ℚ_[q]ˣ)
    (hz : z ∈ LocalNewvector.higherUnits q (max b 1)) : etaLoc q η z = 1 := by
  obtain ⟨-, hball⟩ := hz
  rcases hball with h0 | hle
  · exact absurd h0 (by omega)
  · exact etaLoc_eq_one_of_norm_sub_one_le q hηu (le_max_left _ _) (le_max_right _ _) z hle

theorem det_padicToAdelic (x : GL (Fin 2) ℚ_[q]) :
    Matrix.GeneralLinearGroup.det (AdelicDock.padicToAdelic q x) =
      unitsToIdele q (Matrix.GeneralLinearGroup.det x) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unitsToIdele_apply, Units.coe_map]
  refine Prod.ext ?_ ?_
  ·
    rw [AdelicLevel.finIncl_apply_fst]
    have h := RingHom.map_det (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
      ((AdelicDock.padicToAdelic q x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    rw [AdelicLevel.adeleArch_apply] at h
    rw [h, AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat,
      Matrix.det_one]
  ·
    rw [AdelicLevel.finIncl_apply_snd]
    have h := RingHom.map_det (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)
      ((AdelicDock.padicToAdelic q x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
    rw [AdelicLevel.adeleFin_apply] at h
    rw [h, AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat]
    refine FiniteAdeleRing.ext ℚ fun w => ?_
    have hw := RingHom.map_det (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w)
      ((AdelicDock.padicToFinAdelic q x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    rw [AdelicLevel.finAdeleEval_apply] at hw
    rw [hw, AdelicDock.padicToFinAdelic_apply, AdelicDock.coe_localEmbed]
    by_cases hwq : w = AdelicDock.padicPlace q
    · subst hwq
      rw [AdelicDock.mapMatrix_localMat_self, AdelicLevel.localUnit_apply_self, Units.coe_map,
        ← Matrix.GeneralLinearGroup.val_det_apply, AdelicDock.padicGL, Matrix.GeneralLinearGroup.map_det,
        Units.coe_map]
      rfl
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hwq, Matrix.det_one,
        AdelicLevel.localUnit_apply_of_ne _ _ _ _ hwq]

theorem chiDet_mul (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ η (g * h) =
      AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g * AutomorphicForm.chiDet (𝓞 ℚ) ℚ η h := by
  simp only [AutomorphicForm.chiDet, map_mul, Units.val_mul]

theorem chiDet_ne_zero (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g ≠ 0 :=
  Units.ne_zero _

theorem chiDet_padicToAdelic (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (x : GL (Fin 2) ℚ_[q]) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ η (AdelicDock.padicToAdelic q x) =
      (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) := by
  simp only [AutomorphicForm.chiDet, det_padicToAdelic, etaLoc, MonoidHom.comp_apply]

theorem chiDet_mul_padicToAdelic (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) ℚ_[q]) :
    AutomorphicForm.chiDet (𝓞 ℚ) ℚ η (g * AdelicDock.padicToAdelic q x) =
      AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g * (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) := by
  rw [chiDet_mul, chiDet_padicToAdelic]

theorem norm_det_sub_one_le {B : ℕ} (hB : 1 ≤ B) {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q B) :
    ‖((Matrix.GeneralLinearGroup.det k : ℚ_[q]ˣ) : ℚ_[q]) - 1‖ ≤ (q : ℝ) ^ (-(B : ℤ)) := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q hB] at hk
  set M : Matrix (Fin 2) (Fin 2) ℚ_[q] := (k : Matrix (Fin 2) (Fin 2) ℚ_[q]) with hM
  set r : ℝ := (q : ℝ) ^ (-(B : ℤ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (zpow_neg_lt_one q hB).le
  have h00 : ‖M 0 0 - 1‖ ≤ r := by simpa [Matrix.sub_apply] using hk 0 0
  have h11 : ‖M 1 1 - 1‖ ≤ r := by simpa [Matrix.sub_apply] using hk 1 1
  have h01 : ‖M 0 1‖ ≤ r := by simpa [Matrix.sub_apply] using hk 0 1
  have h10 : ‖M 1 0‖ ≤ r := by simpa [Matrix.sub_apply] using hk 1 0
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hexp : M 0 0 * M 1 1 - M 0 1 * M 1 0 - 1
      = (M 0 0 - 1) * (M 1 1 - 1) + ((M 0 0 - 1) + ((M 1 1 - 1) + -(M 0 1 * M 1 0))) := by ring
  rw [← hM, hexp]
  have hnn := IsUltrametricDist.norm_add_le_max
    ((M 0 0 - 1) * (M 1 1 - 1)) ((M 0 0 - 1) + ((M 1 1 - 1) + -(M 0 1 * M 1 0)))
  refine hnn.trans (max_le ?_ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h00
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h11 ?_)))))
  · rw [norm_mul]
    calc ‖M 0 0 - 1‖ * ‖M 1 1 - 1‖ ≤ r * 1 :=
          mul_le_mul h00 (h11.trans hr1) (norm_nonneg _) hr0
      _ = r := mul_one r
  · rw [norm_neg, norm_mul]
    calc ‖M 0 1‖ * ‖M 1 0‖ ≤ r * 1 := mul_le_mul h01 (h10.trans hr1) (norm_nonneg _) hr0
      _ = r := mul_one r

section Spans

open LocalNewvector

def mulFn (c : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : AdelicFnCarrier ℚ →ₗ[ℂ] AdelicFnCarrier ℚ where
  toFun F := AdelicFnCarrier.mk fun g => c g * F.toFn g
  map_add' F G := AdelicFnCarrier.ext fun g => by
    simp only [AdelicFnCarrier.toFn_mk, AdelicFnCarrier.toFn_add, Pi.add_apply]; ring
  map_smul' a F := AdelicFnCarrier.ext fun g => by
    simp only [AdelicFnCarrier.toFn_mk, AdelicFnCarrier.toFn_csmul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

@[scoped simp] theorem toFn_mulFn (c : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (F : AdelicFnCarrier ℚ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : (mulFn c F).toFn g = c g * F.toFn g := rfl

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

abbrev cTw : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ := AutomorphicForm.chiDet (𝓞 ℚ) ℚ η

abbrev cUn : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => (AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g)⁻¹

theorem mulFn_cUn_smul_mk (g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    mulFn (cUn η) (g₀ • AdelicFnCarrier.mk (AutomorphicForm.fnTwist ℚ η Φ)) =
      (AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g₀ : ℂ) • (g₀ • AdelicFnCarrier.mk Φ) := by
  refine AdelicFnCarrier.ext fun g => ?_
  simp only [toFn_mulFn, AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_mk, AdelicFnCarrier.toFn_csmul,
    Pi.smul_apply, smul_eq_mul, AutomorphicForm.fnTwist_apply, chiDet_mul]
  have h := chiDet_ne_zero η g
  field_simp

theorem mulFn_cTw_smul_mk (g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    mulFn (cTw η) (g₀ • AdelicFnCarrier.mk Φ) =
      (AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g₀ : ℂ)⁻¹ • (g₀ • AdelicFnCarrier.mk (AutomorphicForm.fnTwist ℚ η Φ)) := by
  refine AdelicFnCarrier.ext fun g => ?_
  simp only [toFn_mulFn, AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_mk, AdelicFnCarrier.toFn_csmul,
    Pi.smul_apply, smul_eq_mul, AutomorphicForm.fnTwist_apply, chiDet_mul]
  have h := chiDet_ne_zero η g₀
  field_simp

theorem mulFn_cUn_mulFn_cTw (F : AdelicFnCarrier ℚ) : mulFn (cUn η) (mulFn (cTw η) F) = F := by
  refine AdelicFnCarrier.ext fun g => ?_
  simp only [toFn_mulFn]
  have h := chiDet_ne_zero η g
  field_simp

theorem mulFn_cTw_mulFn_cUn (F : AdelicFnCarrier ℚ) : mulFn (cTw η) (mulFn (cUn η) F) = F := by
  refine AdelicFnCarrier.ext fun g => ?_
  simp only [toFn_mulFn]
  have h := chiDet_ne_zero η g
  field_simp

theorem mulFn_cUn_maps :
    ∀ F ∈ AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ), mulFn (cUn η) F ∈ AdelicSpanSubmodule Φ := by
  intro F hF
  have hle : (AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ)).map (mulFn (cUn η)) ≤ AdelicSpanSubmodule Φ := by
    rw [AdelicSpanSubmodule, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨ψ, ⟨g₀, rfl⟩, rfl⟩
    rw [mulFn_cUn_smul_mk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g₀, rfl⟩)
  exact hle ⟨F, hF, rfl⟩

theorem mulFn_cTw_maps :
    ∀ F ∈ AdelicSpanSubmodule Φ, mulFn (cTw η) F ∈ AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ) := by
  intro F hF
  have hle : (AdelicSpanSubmodule Φ).map (mulFn (cTw η)) ≤ AdelicSpanSubmodule (AutomorphicForm.fnTwist ℚ η Φ) := by
    rw [AdelicSpanSubmodule, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨ψ, ⟨g₀, rfl⟩, rfl⟩
    rw [mulFn_cTw_smul_mk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g₀, rfl⟩)
  exact hle ⟨F, hF, rfl⟩

def untwist : AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ] AdelicSpan Φ :=
  (mulFn (cUn η)).restrict (mulFn_cUn_maps η Φ)

def twist : AdelicSpan Φ →ₗ[ℂ] AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) :=
  (mulFn (cTw η)).restrict (mulFn_cTw_maps η Φ)

@[scoped simp] theorem toFn_untwist (v : AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) :
    AdelicSpan.toFn Φ (untwist η Φ v) = mulFn (cUn η) (AdelicSpan.toFn _ v) := rfl

@[scoped simp] theorem toFn_twist (v : AdelicSpan Φ) :
    AdelicSpan.toFn _ (twist η Φ v) = mulFn (cTw η) (AdelicSpan.toFn Φ v) := rfl

theorem untwist_twist (v : AdelicSpan Φ) : untwist η Φ (twist η Φ v) = v :=
  AdelicSpan.ext Φ (by rw [toFn_untwist, toFn_twist, mulFn_cUn_mulFn_cTw])

theorem untwist_smul (x : GL (Fin 2) ℚ_[q]) (v : AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) :
    untwist η Φ (x • v) = (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) • (x • untwist η Φ v) := by
  refine AdelicSpan.ext Φ (AdelicFnCarrier.ext fun g => ?_)
  rw [AdelicSpan.padic_smul_def, AdelicSpan.padic_smul_def]
  have lhs : AdelicSpan.toFn Φ (untwist η Φ (AdelicDock.padicToAdelic q x • v)) =
      mulFn (cUn η) (AdelicDock.padicToAdelic q x • AdelicSpan.toFn _ v) := rfl
  have rhs : AdelicSpan.toFn Φ ((etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) •
      ((AdelicDock.padicToAdelic q x) • untwist η Φ v)) =
      (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) •
        ((AdelicDock.padicToAdelic q x) • mulFn (cUn η) (AdelicSpan.toFn _ v)) := rfl
  rw [lhs, rhs]
  simp only [toFn_mulFn, AdelicFnCarrier.toFn_smul, AdelicFnCarrier.toFn_csmul, Pi.smul_apply,
    smul_eq_mul, cUn]
  rw [chiDet_mul_padicToAdelic]
  have h1 := chiDet_ne_zero η g
  have h2 : (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

end Spans

section PS

open LocalNewvector

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)

theorem det_borelElem (a₁ a₂ : ℚ_[q]ˣ) (x : ℚ_[q]) :
    Matrix.GeneralLinearGroup.det (borelElem q a₁ a₂ x) = a₁ * a₂ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelElem, Matrix.det_fin_two_of, Units.val_mul]
  ring

theorem isLocallyConstant_etaLoc_det {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} (hηu : EtaUnits q b χ₀ η) :
    IsLocallyConstant fun g : GL (Fin 2) ℚ_[q] => (etaLoc q η (Matrix.GeneralLinearGroup.det g) : ℂ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  set B : ℕ := max b 1 with hB
  refine ⟨(fun k => g₀ * k) '' (FLT.SmoothVectors.gl2CongruenceSubgroup q B : Set (GL (Fin 2) ℚ_[q])),
    ?_, ⟨1, one_mem _, mul_one g₀⟩, ?_⟩
  · have hcont : Continuous fun k : GL (Fin 2) ℚ_[q] => g₀⁻¹ * k := continuous_const.mul continuous_id
    have heq : (fun k => g₀ * k) '' (FLT.SmoothVectors.gl2CongruenceSubgroup q B : Set (GL (Fin 2) ℚ_[q])) =
        (fun k => g₀⁻¹ * k) ⁻¹' (FLT.SmoothVectors.gl2CongruenceSubgroup q B : Set (GL (Fin 2) ℚ_[q])) := by
      ext k
      constructor
      · rintro ⟨k', hk', rfl⟩
        simpa using hk'
      · intro hk
        exact ⟨g₀⁻¹ * k, hk, by group⟩
    rw [heq]
    exact (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q B).preimage hcont
  · rintro _ ⟨k, hk, rfl⟩
    have hk1 : etaLoc q η (Matrix.GeneralLinearGroup.det k) = 1 :=
      etaLoc_eq_one_of_norm_sub_one_le q hηu (le_max_left _ _) (le_max_right _ _) _
        (norm_det_sub_one_le q (le_max_right _ _) hk)
    simp only [map_mul, hk1, mul_one]

def twFn (φ : PSCarrier q μ₁ μ₂) : GL (Fin 2) ℚ_[q] → ℂ :=
  fun g => (etaLoc q η (Matrix.GeneralLinearGroup.det g) : ℂ) * PSCarrier.toFn q μ₁ μ₂ φ g

theorem twFn_mem {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} (hηu : EtaUnits q b χ₀ η) (φ : PSCarrier q μ₁ μ₂) :
    twFn q η μ₁ μ₂ φ ∈ principalSeries q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η) := by
  refine (mem_principalSeries_iff q).mpr ⟨?_, fun a₁ a₂ x g => ?_⟩
  · exact (isLocallyConstant_etaLoc_det q η hηu).mul
      (isLocallyConstant_of_mem_principalSeries q (PSCarrier.toFn_mem q μ₁ μ₂ φ))
  · simp only [twFn, map_mul, det_borelElem, MonoidHom.mul_apply, Units.val_mul,
      apply_borelElem_mul_of_mem_principalSeries q (PSCarrier.toFn_mem q μ₁ μ₂ φ)]
    ring

def tw {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} (hηu : EtaUnits q b χ₀ η) : PSCarrier q μ₁ μ₂ →ₗ[ℂ] PSCarrier q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η) where
  toFun φ := PSCarrier.mk q _ _ ⟨twFn q η μ₁ μ₂ φ, twFn_mem q η μ₁ μ₂ hηu φ⟩
  map_add' φ ψ := PSCarrier.ext q _ _ fun g => by
    show twFn q η μ₁ μ₂ (φ + ψ) g = twFn q η μ₁ μ₂ φ g + twFn q η μ₁ μ₂ ψ g
    simp only [twFn]
    show _ * (PSCarrier.toFn q μ₁ μ₂ φ g + PSCarrier.toFn q μ₁ μ₂ ψ g) = _
    ring
  map_smul' c φ := PSCarrier.ext q _ _ fun g => by
    show twFn q η μ₁ μ₂ (c • φ) g = c * twFn q η μ₁ μ₂ φ g
    simp only [twFn, PSCarrier.toFn_csmul]
    ring

@[scoped simp] theorem toFn_tw {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} (hηu : EtaUnits q b χ₀ η) (φ : PSCarrier q μ₁ μ₂) (g : GL (Fin 2) ℚ_[q]) :
    PSCarrier.toFn q _ _ (tw q η μ₁ μ₂ hηu φ) g =
      (etaLoc q η (Matrix.GeneralLinearGroup.det g) : ℂ) * PSCarrier.toFn q μ₁ μ₂ φ g := rfl

theorem tw_smul {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} (hηu : EtaUnits q b χ₀ η) (x : GL (Fin 2) ℚ_[q]) (φ : PSCarrier q μ₁ μ₂) :
    tw q η μ₁ μ₂ hηu (x • φ) =
      (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ)⁻¹ • (x • tw q η μ₁ μ₂ hηu φ) := by
  refine PSCarrier.ext q _ _ fun g => ?_
  simp only [toFn_tw, PSCarrier.toFn_smul, PSCarrier.toFn_csmul, map_mul, Units.val_mul]
  have h2 : (etaLoc q η (Matrix.GeneralLinearGroup.det x) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem tw_eq_zero_iff {b : ℕ} {χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ} (hηu : EtaUnits q b χ₀ η) (φ : PSCarrier q μ₁ μ₂) :
    tw q η μ₁ μ₂ hηu φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    refine PSCarrier.ext q _ _ fun g => ?_
    have hg := congrArg (fun ψ => PSCarrier.toFn q _ _ ψ g) h
    simp only [toFn_tw] at hg
    have h2 : (etaLoc q η (Matrix.GeneralLinearGroup.det g) : ℂ) ≠ 0 := Units.ne_zero _
    have h0 : PSCarrier.toFn q (μ₁ * etaLoc q η) (μ₂ * etaLoc q η) 0 g = 0 := rfl
    rw [h0] at hg
    have : PSCarrier.toFn q μ₁ μ₂ φ g = 0 := by
      rcases mul_eq_zero.mp hg with h | h
      · exact absurd h h2
      · exact h
    rw [this]; rfl
  · rintro rfl; exact map_zero _

end PS

section Adelic

theorem coe_glArch (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ((AdelicLevel.glArch (𝓞 ℚ) ℚ g : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := rfl

theorem coe_finComponent_glFin (w : HeightOneSpectrum (𝓞 ℚ)) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ((AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ g) : GL (Fin 2) (w.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) := rfl

theorem adelicGL2_ext {g h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (harch : AdelicLevel.glArch (𝓞 ℚ) ℚ g = AdelicLevel.glArch (𝓞 ℚ) ℚ h)
    (hfin : ∀ w, AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ g) =
      AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ h)) : g = h := by
  apply Units.ext
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [← coe_glArch, ← coe_glArch, harch]
  · refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [← coe_finComponent_glFin, ← coe_finComponent_glFin, hfin w]

def qComponent (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (AdelicDock.padicRingEquiv q).symm.toRingHom
    (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g))

theorem padicGL_qComponent (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicDock.padicGL q (qComponent q g) =
      AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply, qComponent, Matrix.GeneralLinearGroup.map_apply]
  exact (AdelicDock.padicRingEquiv q).apply_symm_apply _

def awayPart (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ :=
  (AdelicDock.padicToAdelic q (qComponent q g))⁻¹ * g

theorem finComponent_awayPart_self (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ (awayPart q g)) = 1 := by
  rw [awayPart, map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
    AdelicDock.finComponent_padicToFinAdelic_self, padicGL_qComponent, inv_mul_cancel]

theorem padicToAdelic_mul_awayPart (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    AdelicDock.padicToAdelic q (qComponent q g) * awayPart q g = g := by
  rw [awayPart, mul_inv_cancel_left]

theorem padicToAdelic_mul_comm_of_finComponent_eq_one {g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g) = 1)
    (x : GL (Fin 2) ℚ_[q]) :
    AdelicDock.padicToAdelic q x * g = g * AdelicDock.padicToAdelic q x := by
  refine adelicGL2_ext ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.glArch_padicToAdelic, one_mul, mul_one]
  · intro w
    rw [map_mul, map_mul, map_mul, map_mul, AdelicDock.glFin_padicToAdelic]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw; rw [hg, mul_one, one_mul]
    · rw [AdelicDock.finComponent_padicToFinAdelic_of_ne _ _ hw, one_mul, mul_one]

end Adelic

section SpanFacts

open LocalNewvector

variable {φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

theorem mk_smul_mk (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (h : g • AdelicFnCarrier.mk φ ∈ AdelicSpanSubmodule φ) :
    AdelicSpan.mk φ (g • AdelicFnCarrier.mk φ) h = g • AdelicSpan.self φ :=
  AdelicSpan.ext φ rfl

theorem mk_zero (h : (0 : AdelicFnCarrier ℚ) ∈ AdelicSpanSubmodule φ) : AdelicSpan.mk φ 0 h = 0 :=
  AdelicSpan.ext φ rfl

theorem mk_add (x y : AdelicFnCarrier ℚ) (hx : x ∈ AdelicSpanSubmodule φ) (hy : y ∈ AdelicSpanSubmodule φ)
    (hxy : x + y ∈ AdelicSpanSubmodule φ) :
    AdelicSpan.mk φ (x + y) hxy = AdelicSpan.mk φ x hx + AdelicSpan.mk φ y hy :=
  AdelicSpan.ext φ rfl

theorem mk_csmul (a : ℂ) (x : AdelicFnCarrier ℚ) (hx : x ∈ AdelicSpanSubmodule φ)
    (hax : a • x ∈ AdelicSpanSubmodule φ) :
    AdelicSpan.mk φ (a • x) hax = a • AdelicSpan.mk φ x hx :=
  AdelicSpan.ext φ rfl

theorem mk_toFn (v : AdelicSpan φ) :
    AdelicSpan.mk φ (AdelicSpan.toFn φ v) (v : AdelicSpanSubmodule φ).2 = v :=
  AdelicSpan.ext φ rfl

theorem linearMap_eq_zero_of_forall_translate {N : Type*} [AddCommGroup N] [Module ℂ N]
    (L : AdelicSpan φ →ₗ[ℂ] N)
    (hL : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, L (g • AdelicSpan.self φ) = 0) : L = 0 := by
  have key : ∀ (ψ : AdelicFnCarrier ℚ) (hψ : ψ ∈ AdelicSpanSubmodule φ), L (AdelicSpan.mk φ ψ hψ) = 0 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [mk_smul_mk]; exact hL g
    | zero => rw [mk_zero, map_zero]
    | add x y hx hy ihx ihy => rw [mk_add x y hx hy, map_add, ihx, ihy, add_zero]
    | smul a x hx ih => rw [mk_csmul a x hx, map_smul, ih, smul_zero]
  ext v
  rw [LinearMap.zero_apply, ← mk_toFn v]
  exact key _ _

def qSpan (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Submodule ℂ (AdelicSpan φ) :=
  Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ)

theorem self_mem_qSpan : AdelicSpan.self φ ∈ qSpan q φ :=
  Submodule.subset_span ⟨1, one_smul _ _⟩

theorem smul_mem_qSpan (x : GL (Fin 2) ℚ_[q]) : ∀ w ∈ qSpan q φ, x • w ∈ qSpan q φ := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', rfl⟩ := hw
    exact Submodule.subset_span ⟨x * x', by simp only [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ ih₁ ih₂ => rw [smul_add]; exact add_mem ih₁ ih₂
  | smul a w _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih

theorem qSpan_smooth (K : Subgroup (GL (Fin 2) ℚ_[q])) (hKopen : IsOpen (K : Set (GL (Fin 2) ℚ_[q])))
    (hKfix : ∀ k ∈ K, k • AdelicSpan.self φ = AdelicSpan.self φ) :
    ∀ w ∈ qSpan q φ, ∃ U : Subgroup (GL (Fin 2) ℚ_[q]),
      IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧ ∀ u ∈ U, u • w = w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    refine ⟨K.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hKopen.preimage ?_
      show Continuous fun u : GL (Fin 2) ℚ_[q] => x⁻¹ * u * x⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    · intro u hu
      rw [Subgroup.mem_comap] at hu
      have hk := hKfix _ hu
      show u • x • AdelicSpan.self φ = x • AdelicSpan.self φ
      have hux : u * x = x * (x⁻¹ * u * x⁻¹⁻¹) := by group
      rw [← mul_smul, hux, mul_smul]
      exact congrArg (fun v => x • v) hk
  | zero => exact ⟨⊤, isOpen_univ, fun u _ => smul_zero u⟩
  | add w₁ w₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, ?_, fun u hu => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · rw [smul_add, h₁ u hu.1, h₂ u hu.2]
  | smul a w _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    exact ⟨U, hU, fun u hu => by rw [smul_comm, h u hu]⟩

end SpanFacts

section Generator

open LocalNewvector

variable (η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

theorem toFn_toFn_smul_self (g x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn _ (x • AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ))).toFn g =
      AutomorphicForm.chiDet (𝓞 ℚ) ℚ η (g * x) * Φ (g * x) := rfl

theorem toFn_toFn_self (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn _ (AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ))).toFn g =
      AutomorphicForm.chiDet (𝓞 ℚ) ℚ η g * Φ g := rfl

theorem toFn_toFn_csmul (a : ℂ) (v : AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    (AdelicSpan.toFn _ (a • v)).toFn g = a * (AdelicSpan.toFn _ v).toFn g := rfl

theorem smul_self_eq_self_of {k : GL (Fin 2) ℚ_[q]}
    (hΦk : ∀ x, Φ (x * AdelicDock.padicToAdelic q k) = Φ x)
    (hηk : etaLoc q η (Matrix.GeneralLinearGroup.det k) = 1) :
    k • AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) = AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun g => ?_)
  rw [AdelicSpan.padic_smul_def, toFn_toFn_smul_self, toFn_toFn_self, chiDet_mul_padicToAdelic, hΦk, hηk,
    Units.val_one, mul_one]

theorem centralGL_smul_self {z : ℚ_[q]ˣ}
    (hΦz : ∀ x, Φ (x * AdelicDock.padicToAdelic q (centralGL q z)) = Φ x) :
    centralGL q z • AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) =
      ((etaLoc q η z : ℂ) ^ 2) • AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ) := by
  refine AdelicSpan.ext _ (AdelicFnCarrier.ext fun g => ?_)
  rw [AdelicSpan.padic_smul_def, toFn_toFn_smul_self, toFn_toFn_csmul, toFn_toFn_self, chiDet_mul_padicToAdelic,
    hΦz]
  have hdet : Matrix.GeneralLinearGroup.det (centralGL q z) = z ^ 2 := by
    show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  rw [hdet, map_pow, Units.val_pow_eq_pow_val]
  ring

theorem centralGL_mul_comm (z : ℚ_[q]ˣ) (x : GL (Fin 2) ℚ_[q]) : centralGL q z * x = x * centralGL q z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact Algebra.commutes (z : ℚ_[q]) (x : Matrix (Fin 2) (Fin 2) ℚ_[q])

end Generator

end TwistNewvec
p2m_reactivate "P2MW.S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio.TwistNewvec"

open NumberField LocalNewvector TwistNewvec in
theorem solution
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (q : ℕ) [Fact q.Prime]
    (n₀ : ℕ) (hΦK : ∀ k ∈ LocalNewvector.padicK1 q n₀, ∀ x, Φ (x * AdelicDock.padicToAdelic q k) = Φ x)
    (hΦZ : ∀ (u : ℤ_[q]ˣ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Φ (x * AdelicDock.padicToAdelic q
        (LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) = Φ x)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχ₀compat : ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) =
        χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηu : ∀ u : ℤ_[q]ˣ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u))))
        = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) :
    ∃ (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ)
      (f' : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
      (a : ℕ) (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)),
          f' (x • v) = x • f' v) ∧
      f' ≠ 0 ∧ LocalNewvector.IsUnramified q ν₁ ∧
      LocalNewvector.HasCharConductor q (μ₁⁻¹ * μ₂) a ∧
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] =>
          x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
        (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      ∀ u : ℤ_[q]ˣ,
        LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
          ((μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) : ℂ) ^ 2)⁻¹ • y := by
  classical
  have hηu' : EtaUnits q b χ₀ η := hηu

  set ν₁ : ℚ_[q]ˣ →* ℂˣ := μ₁ * etaLoc q η with hν₁_def
  set ν₂ : ℚ_[q]ˣ →* ℂˣ := μ₂ * etaLoc q η with hν₂_def
  set Φ' := AutomorphicForm.fnTwist ℚ η Φ with hΦ'_def

  set fη : AdelicSpan Φ' →ₗ[ℂ] PSCarrier q ν₁ ν₂ := (tw q η μ₁ μ₂ hηu') ∘ₗ f ∘ₗ (untwist η Φ) with hfη_def
  have hfη_apply : ∀ v, fη v = tw q η μ₁ μ₂ hηu' (f (untwist η Φ v)) := fun v => rfl
  have hfη_equiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : AdelicSpan Φ'), fη (x • v) = x • fη v := by
    intro x v
    rw [hfη_apply, hfη_apply, untwist_smul, map_smul, hfequiv, map_smul, tw_smul, smul_smul,
      mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hfη0 : fη ≠ 0 := by
    intro h
    apply hf0
    ext w
    have h2 : fη (twist η Φ w) = 0 := by rw [h, LinearMap.zero_apply]
    rw [hfη_apply, untwist_twist, tw_eq_zero_iff] at h2
    rw [h2, LinearMap.zero_apply]

  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ, fη (g₀ • AdelicSpan.self Φ') ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hfη0 (linearMap_eq_zero_of_forall_translate fη hall)
  set gq := awayPart q g₀ with hgq_def
  have hgq1 := finComponent_awayPart_self q g₀
  have hcomm : ∀ x : GL (Fin 2) ℚ_[q], AdelicDock.padicToAdelic q x * gq = gq * AdelicDock.padicToAdelic q x :=
    fun x => padicToAdelic_mul_comm_of_finComponent_eq_one q hgq1 x
  have hgqself : fη (gq • AdelicSpan.self Φ') ≠ 0 := by
    intro h0
    apply hg₀
    rw [← padicToAdelic_mul_awayPart q g₀, mul_smul, ← AdelicSpan.padic_smul_def, hfη_equiv, ← hgq_def, h0,
      smul_zero]

  set T : AdelicSpan Φ' →ₗ[ℂ] PSCarrier q ν₁ ν₂ := fη ∘ₗ DistribSMul.toLinearMap ℂ (AdelicSpan Φ') gq with hT_def
  have hT_apply : ∀ v, T v = fη (gq • v) := fun v => rfl
  have hT : ∀ (x : GL (Fin 2) ℚ_[q]) (v : AdelicSpan Φ'), T (x • v) = x • T v := by
    intro x v
    rw [hT_apply, hT_apply, AdelicSpan.padic_smul_def, ← mul_smul, ← hcomm x, mul_smul,
      ← AdelicSpan.padic_smul_def, hfη_equiv]
  have hTself : T (AdelicSpan.self Φ') ≠ 0 := hgqself

  set W : Submodule ℂ (AdelicSpan Φ') := qSpan q Φ' with hW_def
  have hW : ∀ x : GL (Fin 2) ℚ_[q], ∀ w ∈ W, x • w ∈ W := smul_mem_qSpan q
  set B' : ℕ := max (max b 1) n₀ with hB'_def
  have hKfix : ∀ k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q B', k • AdelicSpan.self Φ' = AdelicSpan.self Φ' := by
    intro k hk
    have hk1 : k ∈ padicK1 q n₀ :=
      congruenceK1_antitone (le_max_right _ _) (gl2CongruenceSubgroup_le_padicK1 q B' hk)
    refine smul_self_eq_self_of q η Φ (fun x => hΦK k hk1 x) ?_
    exact etaLoc_eq_one_of_norm_sub_one_le q hηu' ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _)) _
      (norm_det_sub_one_le q ((le_max_right _ _).trans (le_max_left _ _)) hk)
  have hsmooth := qSpan_smooth q (FLT.SmoothVectors.gl2CongruenceSubgroup q B')
    (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q B') hKfix

  obtain ⟨w, hw⟩ : ∃ w : AdelicSpan Φ, f w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf0 (LinearMap.ext fun w => by rw [hall w, LinearMap.zero_apply])
  obtain ⟨c, hc⟩ := PSCarrier.exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero q μ₁ μ₂ (f w) hw
  have hν₁ : IsUnramified q ν₁ := by
    intro z hz
    have hu : unitsCoe q (PadicInt.mkUnits hz) = z := unitsCoe_mkUnits q hz
    rw [hν₁_def, MonoidHom.mul_apply, ← hu, etaLoc_unitsCoe q hηu']
    show μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom (PadicInt.mkUnits hz)) * _ = 1
    rw [hχ₀compat, mul_inv_cancel]
  have hν₁c : HasCharConductor q ν₁ 0 := (hasCharConductor_zero_iff_isUnramified q).mpr hν₁
  set C : ℕ := max c (max b 1) with hC_def
  have hν₂C : ∀ z ∈ higherUnits q C, ν₂ z = 1 := by
    intro z hz
    rw [hν₂_def, MonoidHom.mul_apply, (hc z (higherUnits_antitone q (le_max_left _ _) hz)).2,
      etaLoc_eq_one_of_mem_higherUnits q hηu' z (higherUnits_antitone q (le_max_right _ _) hz), mul_one]
  have hex : ∃ n, ∀ z ∈ higherUnits q n, ν₂ z = 1 := ⟨C, hν₂C⟩
  set n₂ : ℕ := Nat.find hex with hn₂_def
  have hν₂c : HasCharConductor q ν₂ n₂ := by
    refine ⟨Nat.find_spec hex, fun m hm => ?_⟩
    have hmin := Nat.find_min hex hm
    push Not at hmin
    exact hmin

  have hratioν : ν₁⁻¹ * ν₂ = μ₁⁻¹ * μ₂ := by
    refine MonoidHom.ext fun z => Units.ext ?_
    simp only [hν₁_def, hν₂_def, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have h1 : (μ₁ z : ℂ) ≠ 0 := Units.ne_zero _
    have h2 : (etaLoc q η z : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hirr : IsIrreducibleGLRep q (PSCarrier q ν₁ ν₂) :=
    PSCarrier.isIrreducibleGLRep_of_hasCharConductor_of_ratio q hν₁c hν₂c
      (fun hun => absurd (hratioν ▸ hun) hratio)

  have hfin := PSCarrier.finrank_fixedSubmodule_padicK1 q hν₁c hν₂c (0 + n₂)
  rw [Nat.zero_add, Nat.add_sub_cancel_left] at hfin
  haveI : Nontrivial ↥(fixedSubmodule (padicK1 q n₂) (PSCarrier q ν₁ ν₂)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hfin]; exact Nat.one_pos)
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : ↥(fixedSubmodule (padicK1 q n₂) (PSCarrier q ν₁ ν₂)))
  have hw₀ne : (w₀ : PSCarrier q ν₁ ν₂) ≠ 0 := fun h => hw₀ (Subtype.ext h)
  have hWT : ∀ x : GL (Fin 2) ℚ_[q], ∀ v ∈ W.map T, x • v ∈ W.map T := by
    rintro x _ ⟨w', hw', rfl⟩
    exact ⟨x • w', hW x w' hw', hT x w'⟩
  have htop : W.map T = ⊤ := by
    rcases hirr.2 (W.map T) hWT with hbot | htop
    · exfalso
      apply hTself
      have : T (AdelicSpan.self Φ') ∈ W.map T := ⟨_, self_mem_qSpan q, rfl⟩
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact htop
  obtain ⟨v, hvW, hTv⟩ : ∃ v ∈ W, T v = (w₀ : PSCarrier q ν₁ ν₂) := by
    have : (w₀ : PSCarrier q ν₁ ν₂) ∈ W.map T := by rw [htop]; exact Submodule.mem_top
    exact this
  obtain ⟨y, hyW, hyfix, hTy⟩ :=
    exists_mem_fixedSubmodule_and_map_eq_of_map_mem_fixedSubmodule q ν₁ ν₂ T hT W hW hsmooth n₂ hvW
      (by rw [hTv]; exact w₀.2)
  have hy0 : y ≠ 0 := by
    intro h
    apply hw₀ne
    rw [← hTv, ← hTy, h, map_zero]

  have hcentW : ∀ (u : ℤ_[q]ˣ), ∀ w' ∈ W,
      centralGL q (unitsCoe q u) • w' = ((μ₁ (unitsCoe q u) : ℂ) ^ 2)⁻¹ • w' := by
    intro u w' hw'
    have hval : ((etaLoc q η (unitsCoe q u) : ℂ) ^ 2) = ((μ₁ (unitsCoe q u) : ℂ) ^ 2)⁻¹ := by
      rw [etaLoc_unitsCoe q hηu', Units.val_inv_eq_inv_val, inv_pow, ← hχ₀compat]
    induction hw' using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨x, rfl⟩ := hw'
      show centralGL q (unitsCoe q u) • x • AdelicSpan.self Φ' = _
      rw [← mul_smul, centralGL_mul_comm, mul_smul, centralGL_smul_self q η Φ (hΦZ u), hval, smul_comm]
    | zero => rw [smul_zero, smul_zero]
    | add w₁ w₂ _ _ ih₁ ih₂ => rw [smul_add, smul_add, ih₁, ih₂]
    | smul a w' _ ih => rw [smul_comm, ih, smul_comm]

  have hagree : ∀ z : ℚ_[q]ˣ, ‖(z : ℚ_[q])‖ = 1 → ν₂ z = (μ₁⁻¹ * μ₂) z := by
    intro z hz
    have hu : unitsCoe q (PadicInt.mkUnits hz) = z := unitsCoe_mkUnits q hz
    rw [hν₂_def, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, ← hu, etaLoc_unitsCoe q hηu']
    rw [show μ₁ (unitsCoe q (PadicInt.mkUnits hz)) = μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom (PadicInt.mkUnits hz))
      from rfl, hχ₀compat, mul_comm]
  have hcond : HasCharConductor q (μ₁⁻¹ * μ₂) n₂ := by
    refine ⟨fun z hz => ?_, fun m hm => ?_⟩
    · rw [← hagree z hz.1]; exact hν₂c.1 z hz
    · obtain ⟨z, hz, hne⟩ := hν₂c.2 m hm
      exact ⟨z, hz, by rwa [← hagree z hz.1]⟩

  exact ⟨ν₁, ν₂, fη, n₂, y, hfη_equiv, hfη0, hν₁, hcond, hyW, hy0, hyfix, fun u => hcentW u y hyW⟩

end
p2m_reactivate "P2MW.S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio.TwistNewvec"

end S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
end P2MW
export P2MW.S_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio (solution)
