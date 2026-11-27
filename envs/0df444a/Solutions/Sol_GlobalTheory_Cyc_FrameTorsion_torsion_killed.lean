-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.torsion_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:47.925701+00:00
-- url     : https://prove2.me/submissions/6e50fe11-46ad-4a5c-9df3-46af2f4e185f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGeneratorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleTwistCoboundaryOnBall
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_hinf_le_gj
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_algebraMap_eq
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_norm_l_lt
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_ohat_norm
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_conj_hinf
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_add
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_sub
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_zero
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_pow
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_ball_add
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_ball_sub
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_ball_pow
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_hinf
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_modify
import Theorems.Thm_GlobalTheory_CycCoinv_algebraMap_mem
import Theorems.Thm_GlobalTheory_CycEigen_hinf_le_gj
import Theorems.Thm_GlobalTheory_CycEigen_norm_l_lt
import Theorems.Thm_GlobalTheory_CycEigen_ohat_norm
import Theorems.Thm_GlobalTheory_T_cocycle_vanishing_on_fixingSubgroup_determined_by_generator
import Theorems.Thm_GlobalTheory_T_cyclotomicTower_fixed_iff_mem_completedIntegers
import Theorems.Thm_GlobalTheory_T_cyclotomic_tate_maximalIdeal_kills_first_cohomology
import Theorems.Thm_GlobalTheory_T_torsion_coinvariants_twistedCyclotomicGenerator
import Theorems.Thm_GlobalTheory_TateDecomp_norm_l_lt
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FrameTorsion
variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {i : ℤ}
variable {K : FinExt l} {m : ℕ} {g : GQ l}
namespace GlobalTheory.Cyc.FrameTorsion
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (c : GQ l → Fin r → PadicComplex l) (k : ℕ), CocOn (Gj K m) (twAct act χ i U) (ball l r) c → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ k • c σ) → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ (1 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • c σ) := by
  intro l hl act χ ha hχ K m r hm U g hU J hJ i c k hc hk
  set N : ℕ := max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i))) with hN
  have hHG : ∀ h ∈ Hinf K, h ∈ Gj K m := fun h hh => hinf_le_gj K m hh
  have hgG : g ∈ Gj K m := hU.1.1

  have hHc : CocOn (Hinf K) (fun h y a => act h (y a)) (ball l r) c := by
    refine ⟨hc.1.mono (fun h hh => hHG h hh), fun h hh => hc.2.1 h (hHG h hh), ?_⟩
    intro h hh h' hh'
    rw [hc.2.2 h (hHG h hh) h' (hHG h' hh'), tw_hinf hχ hU hh]

  have hlC : (l : PadicComplex l) ∈ inC (Kinf K) :=
    ⟨algebraMap ℚ_[l] (Om l) (l : ℚ_[l]), IntermediateField.algebraMap_mem _ _,
      (algebraMap_eq (l := l) (l : ℚ_[l])).symm.trans (map_natCast _ l)⟩
  obtain ⟨x1, hx1, hx1e⟩ := GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act ha K r (l : PadicComplex l) hlC norm_l_lt c hHc

  obtain ⟨c1, hc1def⟩ : ∃ c1 : GQ l → Fin r → PadicComplex l,
      c1 = fun σ => (l : PadicComplex l) ^ 1 • c σ - (twAct act χ i U σ x1 - x1) := ⟨_, rfl⟩
  have hc1 : CocOn (Gj K m) (twAct act χ i U) (ball l r) c1 := by
    rw [hc1def]
    exact modify ha hχ hU 1 hc hx1
  have hc1H : ∀ h ∈ Hinf K, c1 h = 0 := by
    intro h hh
    have e := hx1e h hh
    simp only at e
    simp only [hc1def, pow_one, e, tw_hinf hχ hU hh]
    exact sub_self _

  have hw : ∀ a, c1 g a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (c1 g a) (hc1.2.1 g hgG a)).1 ?_
    intro h hh
    have hh' : g⁻¹ * h * g ∈ Hinf K := conj_hinf hχ K m hgG hh
    have e1 : c1 (g * (g⁻¹ * h * g)) = c1 g := by
      rw [hc1.2.2 g hgG _ (hHG _ hh'), hc1H _ hh', tw_zero, add_zero]
    have e2 : c1 (g * (g⁻¹ * h * g)) = fun a => act h (c1 g a) := by
      have e3 : g * (g⁻¹ * h * g) = h * g := by group
      rw [e3, hc1.2.2 h (hHG h hh) g hgG, hc1H h hh, zero_add, tw_hinf hχ hU hh]
    exact congrFun (e2.symm.trans e1) a

  obtain ⟨x0, hx0, hx0e⟩ := hk
  obtain ⟨x2, hx2def⟩ : ∃ x2 : Fin r → PadicComplex l,
      x2 = (l : PadicComplex l) ^ 1 • x0 - (l : PadicComplex l) ^ k • x1 := ⟨_, rfl⟩
  have hx2b : x2 ∈ ball l r := by
    rw [hx2def]
    exact ball_sub (ball_pow 1 hx0) (ball_pow k hx1)
  have hcob1 : ∀ σ ∈ Gj K m, (l : PadicComplex l) ^ k • c1 σ = twAct act χ i U σ x2 - x2 := by
    intro σ hσ
    have e := hx0e σ hσ
    simp only at e
    simp only [hc1def, hx2def]
    rw [tw_sub, tw_pow, tw_pow, smul_sub, smul_sub, smul_comm ((l : PadicComplex l) ^ k) ((l : PadicComplex l) ^ 1) (c σ), e, smul_sub]
    abel
  have hx2O : ∀ a, x2 a ∈ Ohat K := by
    intro a
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (x2 a) (hx2b a)).1 ?_
    intro h hh
    have e := hcob1 h (hHG h hh)
    rw [hc1H h hh, smul_zero, tw_hinf hχ hU hh] at e
    have e' := congrFun e a
    simp only [Pi.zero_apply, Pi.sub_apply] at e'
    exact sub_eq_zero.1 e'.symm

  obtain ⟨y, hyO, hye⟩ := GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator l act χ ha hχ K m r hm U g hU J hJ i (c1 g) x2 k hw hx2O
    (hcob1 g hgG).symm
  rw [← hN] at hye
  have hyb : y ∈ ball l r := fun a => ohat_norm K (hyO a)
  have hyfix : ∀ h ∈ Hinf K, twAct act χ i U h y = y := by
    intro h hh
    rw [tw_hinf hχ hU hh]
    funext a
    exact (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K (y a) (hyb a)).2 (hyO a) h hh

  obtain ⟨d, hddef⟩ : ∃ d : GQ l → Fin r → PadicComplex l,
      d = fun σ => (l : PadicComplex l) ^ N • c1 σ - (twAct act χ i U σ y - y) := ⟨_, rfl⟩
  have hd : CocOn (Gj K m) (twAct act χ i U) (ball l r) d := by
    rw [hddef]
    exact modify ha hχ hU N hc1 hyb
  have hdU : CocOn (Gj K m) (twAct act χ i U) Set.univ d := ⟨hd.1, fun _ _ => Set.mem_univ _, hd.2.2⟩
  have hdH : ∀ h ∈ Hinf K, d h = 0 := by
    intro h hh
    simp only [hddef, hc1H h hh, hyfix h hh, smul_zero, sub_self]
  have hdg : d g = 0 := by
    simp only [hddef]
    rw [hye, sub_self]
  have hd0 := (GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator l act χ ha hχ K m r hm U g hU i).1 d hdU hdH hdg

  refine ⟨y + (l : PadicComplex l) ^ N • x1, ball_add hyb (ball_pow N hx1), ?_⟩
  intro σ hσ
  have e1 := hd0 σ hσ
  simp only [hddef, hc1def] at e1
  rw [smul_sub, smul_sub] at e1
  have e2 := sub_eq_zero.1 e1
  have key : (l : PadicComplex l) ^ N • (l : PadicComplex l) ^ 1 • c σ
      = (twAct act χ i U σ y - y)
        + ((l : PadicComplex l) ^ N • twAct act χ i U σ x1 - (l : PadicComplex l) ^ N • x1) := by
    rw [← e2]
    abel
  simp only
  rw [tw_add, tw_pow, pow_add, mul_smul, smul_comm ((l : PadicComplex l) ^ 1) ((l : PadicComplex l) ^ N) (c σ), key]
  abel
end GlobalTheory.Cyc.FrameTorsion
