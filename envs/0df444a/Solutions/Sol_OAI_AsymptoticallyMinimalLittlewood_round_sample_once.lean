-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.round_sample_once
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:08:04.467207+00:00
-- url     : https://prove2.me/submissions/6357bfae-f678-4c7d-8011-ba534a591eff

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Main.lean:L130-L177
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.round_sample_once. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_defect_rounding

-- ---- from OAI.Analysis.Littlewood.Main ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators
lemma unitCircle_parameter {z : ℂ} (hz : ‖z‖=1) :
    ∃ t∈Set.Icc (0:ℝ) 1, z=realPhase (2*Real.pi*t) := by
  let Z : Circle := ⟨z,by change dist z 0=1; simpa using hz⟩
  let u := (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).symm Z
  let t := AddCircle.equivIco (1:ℝ) 0 u
  refine ⟨t.val,⟨t.property.1,by simpa using t.property.2.le⟩,?_⟩
  have hu : (t.val : UnitAddCircle)=u := AddCircle.coe_equivIco
  have hs : Circle.exp (2*Real.pi*t.val)=Z := by
    rw [show 2*Real.pi*t.val=2*Real.pi/(1:ℝ)*t.val by ring]
    rw [← AddCircle.toCircle_apply_mk,hu,← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply Z
  have hcoe := congrArg (fun w : Circle ↦ (w : ℂ)) hs
  simpa only [Circle.coe_exp,realPhase,mul_comm] using hcoe.symm

lemma littlewood_phase {N : ℕ} (X : Fin N → ℝ) (t : ℝ) :
    littlewoodValue X (realPhase (2*Real.pi*t))=
      ∑ k : Fin N, (X k : ℂ)*realPhase (2*Real.pi*t*k) := by
  unfold littlewoodValue
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [realPhase,← Complex.exp_nat_mul,realPhase]
  congr 1
  push_cast
  ring

end
end AsymptoticallyMinimalLittlewood
namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped Topology
open Filter

lemma entropy_small_defect {δ N u : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20)
    (hN : 0<N) (hu : 0≤u) (hub : u≤4*δ*N) :
    u*Real.log (80*N/u)≤4*δ*N*Real.log (20/δ) := by
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this ⊢
    exact this
  have hL : 1≤Real.log (20/δ) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4)
      (show 4≤20/δ by apply (le_div_iff₀ hδ).mpr; linarith)
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num at hh
    linarith
  by_cases hz : u=0
  · rw [hz]
    simp only [zero_mul]
    positivity
  have hup : 0<u := lt_of_le_of_ne hu (Ne.symm hz)
  have hb : 0<4*δ*N := by positivity
  have hsplit : Real.log (80*N/u)=Real.log (20/δ)+Real.log ((4*δ*N)/u) := by
    rw [← Real.log_mul (by positivity : 20/δ≠0) (by positivity : (4*δ*N)/u≠0)]
    congr 1
    field_simp
    ring
  have hs : u*Real.log ((4*δ*N)/u)≤4*δ*N-u := by
    calc
      _ ≤ u*((4*δ*N)/u-1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu
      _ = _ := by field_simp
  have hm := mul_le_mul_of_nonneg_right hub (sub_nonneg.mpr hL)
  rw [hsplit,mul_add]
  nlinarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

lemma defect_from_energy {N : ℕ} (_hN : 1≤N) {δ : ℝ} (X : Fin N → ℝ)
    (hX : ∀ k, |X k|≤1)
    (hE : (1-8*δ)*(N : ℝ)≤∑ k, (X k)^2) :
    0≤defectMass X ∧ defectMass X≤4*δ*N := by
  have hμ : 0≤defectMass X := div_nonneg
    (Finset.sum_nonneg (fun k _ ↦ sub_nonneg.mpr (hX k))) (by norm_num)
  have hs : (∑ k, (1-|X k|))≤∑ k, (1-(X k)^2) := by
    apply Finset.sum_le_sum
    intro k _
    have hh := mul_nonneg (abs_nonneg (X k)) (sub_nonneg.mpr (hX k))
    nlinarith [sq_abs (X k)]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hs
  refine ⟨hμ,?_⟩
  dsimp [defectMass]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  nlinarith

/-- At a fixed positive length, energy and the full-circle relaxed bound imply
an actual real signing with the stated normalized error. -/
lemma round_sample_once {N : ℕ} (hN : 1≤N) {δ K C : ℝ}
    (hδ : 0<δ) (hδ20 : δ<1/20) (X : Fin N → ℝ)
    (hX : ∀ k, |X k|≤1)
    (hE : (1-8*δ)*(N : ℝ)≤∑ k, (X k)^2)
    (hmax : ∀ t∈Set.Icc (0:ℝ) 1,
      ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X k : ℂ)*realPhase (2*Real.pi*t*k)‖≤K+C/N) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧ ∀ z : ℂ, ‖z‖=1 →
      ‖littlewoodValue ε z‖/Real.sqrt N≤
        K+C/N+196608*(1/Real.sqrt N+2*Real.sqrt (δ*Real.log (20/δ))) := by
  obtain ⟨ε,hε,hround⟩ := defect_rounding hN X hX
  refine ⟨ε,hε,?_⟩
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNs : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hDL : 0≤δ*Real.log (20/δ) := mul_nonneg hδ.le
    (Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith)))
  obtain ⟨hμ0,hμb⟩ := defect_from_energy hN X hX hE
  have hentr := entropy_small_defect hδ hδ20 hNr hμ0 hμb
  have hroot : Real.sqrt (defectMass X*Real.log (80*(N : ℝ)/defectMass X))≤
      2*Real.sqrt (δ*Real.log (20/δ))*Real.sqrt N := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,mul_pow,Real.sq_sqrt hDL,Real.sq_sqrt hNr.le]
    nlinarith
  intro z hz
  obtain ⟨t,ht,rfl⟩ := unitCircle_parameter hz
  have hm := hmax t ht
  rw [← littlewood_phase] at hm
  have hn : ‖(1/(Real.sqrt N : ℂ))*littlewoodValue X (realPhase (2*Real.pi*t))‖=
      ‖littlewoodValue X (realPhase (2*Real.pi*t))‖/Real.sqrt N := by
    rw [norm_mul,norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hNs]
    ring
  rw [hn] at hm
  have hr := hround (realPhase (2*Real.pi*t)) (by simp)
  have hr' : ‖littlewoodValue ε (realPhase (2*Real.pi*t))-
      littlewoodValue X (realPhase (2*Real.pi*t))‖≤
        196608*(1+2*Real.sqrt (δ*Real.log (20/δ))*Real.sqrt N) := by
    exact hr.trans (by nlinarith)
  have hd := div_le_div_of_nonneg_right hr' hNs.le
  have he : (196608*(1+2*Real.sqrt (δ*Real.log (20/δ))*Real.sqrt N))/Real.sqrt N=
      196608*(1/Real.sqrt N+2*Real.sqrt (δ*Real.log (20/δ))) := by
    field_simp
  rw [he] at hd
  have ht := div_le_div_of_nonneg_right
    (norm_le_norm_sub_add (littlewoodValue ε (realPhase (2*Real.pi*t)))
      (littlewoodValue X (realPhase (2*Real.pi*t)))) hNs.le
  rw [add_div] at ht
  linarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open scoped BigOperators Topology
open Filter


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.round_sample_once := @_root_.OAI.AsymptoticallyMinimalLittlewood.round_sample_once
