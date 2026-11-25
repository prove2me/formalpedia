-- Prove2me | solution 1 for GlobalTheory.LabelsAgree.defect_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:12.877287+00:00
-- url     : https://prove2.me/submissions/204ce3c6-7654-4395-be87-80eef74ec4e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_exists
import Theorems.Thm_GlobalTheory_LabelsAgree_tr_txT
import Theorems.Thm_GlobalTheory_LabelsAgree_exists_char_root
import Theorems.Thm_GlobalTheory_LabelsAgree_exists_good
import Theorems.Thm_GlobalTheory_LabelsAgree_tendsto_txT
import Theorems.Thm_GlobalTheory_LabelsAgree_eq_one_of_sums
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_pow
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_injective
import Theorems.Thm_GlobalTheory_Ex_txT_shift
import Theorems.Thm_GlobalTheory_T_norm_rep_generators_and_thetaSeriesTerm
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.LabelsAgree
namespace GlobalTheory.LabelsAgree
theorem _root_.solution {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {n g : ℕ} (ho : Odd n) (hn : ‖(n : C)‖ = 1) (hI : N.Int q)
    (hT : N.Tors n g) (μ : Match N N' n) (J : NumD.Iso N N') (hl : (J.lam : C) = μ.c₀) {j : ℕ} (hj : j ≠ 0)
    {x : N.X} (hx : ∀ z, z ≠ 0 → q x < q (x + (n ^ j) ^ 2 • z)) {d : N'.QT ((n ^ j) ^ 2)}
    (hd : Defect μ J ((n ^ j) ^ 2) x d) : d.1.2.s (J.e x) ^ (((n ^ j) ^ 2 - 1) / 2 + 1) = 1 := by
  have hnC : (n : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨p, hp, hth⟩ := exists_good hnC hT hj x
  have htx := μ.tx j
  have hmn : ‖((n ^ j : ℕ) : C)‖ = 1 := by rw [Nat.cast_pow, norm_pow, hn, one_pow]
  have hm : Odd (n ^ j) := ho.pow
  generalize n ^ j = m at *
  have hm0 : m ≠ 0 := hm.pos.ne'
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff d.1.2).2 hd.2.1
  have ht'k : t' ^ m ^ 2 = 1 := by
    apply N'.tor_injective
    rw [N'.tor_pow, ht', N'.mem_QT.1 d.2, hd.1, toAdd_one, N'.io_zero, N'.tor_one]
  let τ : Multiplicative N.X →* Cˣ := (t'.comp (AddMonoidHom.toMultiplicative J.e.toAddMonoidHom)) ^ m
  have hτ : ∀ χ, τ (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd (J.e χ)) ^ m := fun _ => rfl
  have hτm : τ ^ m = 1 := MonoidHom.ext fun χ => by
    change (t' (Multiplicative.ofAdd (J.e χ.toAdd)) ^ m) ^ m = 1
    rw [← pow_mul, ← sq, TorsionFourier.apply_pow_eq_one ht'k]
  have hnorm := (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p
  have h00 : ‖N.txT m p 0‖ = Real.exp (-(q x / (m : ℝ) ^ 2)) := by
    rw [hnorm, N.c_zero, one_mul, hth, mul_one, smul_zero, add_zero, hp]
  rw [← ht', NumD.torus_generator_apply]
  apply Units.ext
  rw [Units.val_one]
  refine eq_one_of_sums hmn (N.txT m p) (tendsto_txT hI hm p) ?_ (fun z hz => ?_) _ τ hτm fun u hu => ?_
  · rw [← norm_pos_iff, h00]; exact Real.exp_pos _
  · rw [h00, hnorm, hp, smul_smul, ← sq]
    refine (mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)).trans_lt (Real.exp_lt_exp.2 (neg_lt_neg ?_))
    exact div_lt_div_of_pos_right (hx z hz) (by positivity)
  · obtain ⟨t, rfl⟩ := exists_char_root u hm0
    have ht : t ^ m ^ 2 = 1 := by rw [sq, pow_mul, hu]
    obtain ⟨a, ha⟩ := tr_exists J (p * N.qTor t ht)
    have hpx : (p * N.qTor t ht).1.1 = p.1.1 := mul_one _
    have h1 := htx _ _ (hd.2.2 _ a (by rw [hpx, hp]) ha)
    have hay : a.1.1 = Multiplicative.ofAdd (J.e x) := by
      rw [← hp, ← hpx, ← ha.1]; rfl
    have hpy : p.1.1 = Multiplicative.ofAdd x := by rw [← hp]; rfl
    have h2 : ∀ χ, N.txT m (p * N.qTor t ht) χ = (t (Multiplicative.ofAdd x) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) *
        (N.txT m p χ * ((t ^ m) (Multiplicative.ofAdd χ) : C)) := fun χ => by
      rw [(GlobalTheory.Ex.txT_shift C N m hm p (p * N.qTor t ht) χ).2 t hpx rfl, hpy, toAdd_ofAdd, ofAdd_add, ofAdd_nsmul,
        map_mul, map_pow, MonoidHom.pow_apply]
      push_cast
      ring
    have h3 : ∀ χ, N'.txT m (a * d) (J.e χ) = μ.c₀ * ((t (Multiplicative.ofAdd x) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) *
        (((t' (Multiplicative.ofAdd (J.e x)) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) : C) * (τ (Multiplicative.ofAdd χ) : C) *
          N.txT m p χ * ((t ^ m) (Multiplicative.ofAdd χ) : C))) := fun χ => by
      rw [(GlobalTheory.Ex.txT_shift C N' m hm a (a * d) (J.e χ)).2 t' (by change a.1.1 * d.1.1 = _; rw [hd.1, mul_one])
        (by rw [ht']; rfl), tr_txT J hm ha, h2, hl, hay, toAdd_ofAdd, ofAdd_add, ofAdd_nsmul,
        map_mul, map_pow, hτ]
      push_cast
      ring
    rw [NumD.tx, NumD.tx, ← J.e.toEquiv.tsum_eq] at h1
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, h3, tsum_mul_left] at h1
    exact mul_left_cancel₀ (Units.ne_zero _) (mul_left_cancel₀ μ.c₀_ne h1)
end GlobalTheory.LabelsAgree
