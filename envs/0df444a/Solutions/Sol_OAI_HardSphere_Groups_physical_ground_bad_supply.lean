-- Prove2me | solution 1 for OAI.HardSphere.Groups.physical_ground_bad_supply
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:20:07.404999+00:00
-- url     : https://prove2.me/submissions/05fcfe2a-f9fc-4537-bf61-50ada80546ab

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_CellOrbital_grid_stationary_low_above
import Theorems.Thm_OAI_HardSphere_Groups_canonical_supply_counts
import Theorems.Thm_OAI_HardSphere_Groups_grid_close_tail
import Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_probability
import Theorems.Thm_OAI_HardSphere_ShiftVisits_ground_excessVisitors_tail
import Theorems.Thm_OAI_HardSphere_ShiftVisits_ground_longVisitors_tail
import Theorems.Thm_OAI_HardSphere_ShiftVisits_interacting_visit_mgf_uniform

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_Sampling
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
attribute [local instance] Classical.propDecidable

lemma uniform_map_apply {A B : Type*} [Fintype A] [Nonempty A] (f : A→B) (b : B) :
    ((PMF.uniformOfFintype A).map f) b=
      (Nat.card {a // f a=b}:ℝ≥0∞)*(Fintype.card A:ℝ≥0∞)⁻¹ := by
  simp [PMF.map_apply,tsum_fintype,Finset.sum_ite,Nat.card_eq_fintype_card,Fintype.card_subtype,eq_comm]

lemma pmf_eq_uniform_of_constant {A : Type*} [Fintype A] [Nonempty A]
    (P : PMF A) (h : ∀a b,P a=P b) : P=PMF.uniformOfFintype A := by
  ext a
  rw [PMF.uniformOfFintype_apply]
  have hs : (Fintype.card A:ℝ≥0∞)*P a=1 := by
    have hp := P.tsum_coe
    rw [tsum_fintype] at hp
    calc
      _ = ∑ b : A, P a := by simp
      _ = ∑ b : A, P b := Finset.sum_congr rfl (fun b _ ↦ h a b)
      _ = 1 := hp
  have hcard : (Fintype.card A:ℝ≥0∞)≠0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    P a = (Fintype.card A:ℝ≥0∞)⁻¹*((Fintype.card A:ℝ≥0∞)*P a) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel hcard (by simp),one_mul]
    _ = _ := by rw [hs,mul_one]

lemma uniform_map_of_equal_fibers {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (f : A→B)
    (h : ∀b c,Nat.card {a // f a=b}=Nat.card {a // f a=c}) :
    (PMF.uniformOfFintype A).map f=PMF.uniformOfFintype B := by
  apply pmf_eq_uniform_of_constant
  intro b c
  rw [uniform_map_apply,uniform_map_apply,h b c]

lemma embedding_restriction_uniform {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    [Nonempty (B↪V)] [Nonempty (A↪V)] (q : A↪B) :
    (PMF.uniformOfFintype (B↪V)).map (fun f ↦ q.trans f)=PMF.uniformOfFintype (A↪V) := by
  apply uniform_map_of_equal_fibers
  intro g h
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair g h g.injective h.injective
  let e : {f : B↪V // q.trans f=g} ≃ {f : B↪V // q.trans f=h} :=
    { toFun := fun f ↦ ⟨f.val.trans σ.toEmbedding, by
        ext a
        change σ (f.val (q a))=h a
        have hf := congrArg (fun k : A↪V ↦ k a) f.property
        exact (congrArg σ hf).trans (hσ a)⟩
      invFun := fun f ↦ ⟨f.val.trans σ.symm.toEmbedding,by
        ext a
        change σ.symm (f.val (q a))=g a
        have hf := congrArg (fun k : A↪V ↦ k a) f.property
        change f.val (q a)=h a at hf
        rw [hf,←hσ a,σ.symm_apply_apply]⟩
      left_inv := by intro f; apply Subtype.ext; ext b; exact σ.symm_apply_apply (f.val b)
      right_inv := by intro f; apply Subtype.ext; ext b; exact σ.apply_symm_apply (f.val b) }
  exact Nat.card_congr e

lemma descFactorial_ratio_le (b n k : ℕ) (hbn : b≤n) (hkn : k≤n) :
    (b.descFactorial k:ℝ)/(n.descFactorial k:ℝ)≤((b:ℝ)/(n:ℝ))^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hkb : k+1≤b
    · have hk : k≤n := by omega
      have hkn' : k<n := by omega
      have hkb' : k≤b := by omega
      have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      have hnk : (0:ℝ)<(n:ℝ)-k := sub_pos.mpr (by exact_mod_cast hkn')
      have hb0 : (0:ℝ)≤b := Nat.cast_nonneg _
      have hnd : (0:ℝ)<n.descFactorial k := by exact_mod_cast Nat.descFactorial_pos.mpr hk
      have hfactor : ((b:ℝ)-k)/((n:ℝ)-k)≤(b:ℝ)/n := by
        apply (div_le_div_iff₀ hnk hn0).mpr
        have hbn' : (b:ℝ)≤n := by exact_mod_cast hbn
        nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
      rw [Nat.descFactorial_succ,Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_mul,
        Nat.cast_sub hkb',Nat.cast_sub hk,←div_mul_div_comm,pow_succ]
      calc
        _ ≤ ((b:ℝ)/n)*(((b:ℝ)/(n:ℝ))^k) :=
          mul_le_mul hfactor (ih hk) (div_nonneg (Nat.cast_nonneg _) hnd.le) (div_nonneg hb0 hn0.le)
        _ = _ := mul_comm _ _
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega : b<k+1)]
      simpa using pow_nonneg (div_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg n)) (k+1)

lemma all_bad_card {A V : Type*} [Fintype A] [Fintype V] (B : Set V) :
    Nat.card {f : A↪V // ∀a,f a∈B}=(Nat.card B).descFactorial (Fintype.card A) := by
  let e : (A↪B) ≃ {f : A↪V // ∀a,f a∈B} :=
    { toFun := fun f ↦ ⟨f.trans ⟨Subtype.val,Subtype.val_injective⟩,fun a ↦ (f a).property⟩
      invFun := fun f ↦ ⟨fun a ↦ ⟨f.val a,f.property a⟩,fun a b h ↦ f.val.injective (congrArg Subtype.val h)⟩
      left_inv := by intro f; ext a; rfl
      right_inv := by intro f; apply Subtype.ext; ext a; rfl }
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_embedding_eq]

lemma uniform_all_bad {A V : Type*} [Fintype A] [Fintype V] [Nonempty V] [Nonempty (A↪V)]
    (B : Set V) :
    (PMF.uniformOfFintype (A↪V)).toOuterMeasure {f | ∀a,f a∈B}≤
      ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^(Fintype.card A) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,←Nat.card_eq_fintype_card]
  change (Nat.card {f : A↪V // ∀a,f a∈B}:ℝ≥0∞)/_≤_
  rw [all_bad_card (A:=A) B,Fintype.card_embedding_eq]
  have hkn : Fintype.card A≤Fintype.card V :=
    Fintype.card_le_of_embedding (Classical.choice (inferInstance:Nonempty (A↪V)))
  have hd0 : ((Fintype.card V).descFactorial (Fintype.card A):ℝ≥0∞)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkn).ne'
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) hd0) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
  rw [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  simp only [ENNReal.toReal_natCast]
  exact descFactorial_ratio_le _ _ _ (by
    classical
    let : Fintype B := Fintype.ofFinite B
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective (fun x : B ↦ (x:V)) Subtype.val_injective) hkn

lemma uniform_positions_bad {A V : Type*} [Fintype A] [Fintype V] [Nonempty V]
    [Nonempty (A↪V)] (B : Set V) (s : Finset A) :
    (PMF.uniformOfFintype (A↪V)).toOuterMeasure {f | ∀a∈s,f a∈B}≤
      ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^s.card := by
  classical
  let q : s↪A := ⟨Subtype.val,Subtype.val_injective⟩
  let : Nonempty (s↪V) := ⟨q.trans (Classical.choice (inferInstance : Nonempty (A↪V)))⟩
  have he := embedding_restriction_uniform (V:=V) q
  have hp := congrArg (fun P : PMF (s↪V) ↦ P.toOuterMeasure {g | ∀a,g a∈B}) he
  rw [PMF.toOuterMeasure_map_apply] at hp
  have seteq : (fun f : A↪V ↦ q.trans f) ⁻¹' {g | ∀a,g a∈B}={f | ∀a∈s,f a∈B} := by
    ext f
    change (∀a : s,f a.val∈B)↔∀a∈s,f a∈B
    exact ⟨fun h a ha ↦ h ⟨a,ha⟩,fun h a ↦ h a.val a.property⟩
  rw [seteq] at hp
  rw [hp]
  simpa using uniform_all_bad (A:=s) B

lemma uniform_bad_count {A V : Type*} [Fintype A] [Fintype V] [Nonempty V]
    [Nonempty (A↪V)] (B : Set V) (m : ℕ) :
    (PMF.uniformOfFintype (A↪V)).toOuterMeasure
      {f | m≤(Finset.univ.filter (fun a ↦ f a∈B)).card}≤
      (2:ℝ≥0∞)^(Fintype.card A)*
        ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m := by
  classical
  let E : Finset A→Set (A↪V) := fun s ↦ {f | s.card=m ∧ ∀a∈s,f a∈B}
  have hsub : {f : A↪V | m≤(Finset.univ.filter (fun a ↦ f a∈B)).card}⊆⋃s,E s := by
    intro f hf
    obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq hf
    exact mem_iUnion.mpr ⟨s,hcard,fun a ha ↦ (Finset.mem_filter.mp (hs ha)).2⟩
  have hE (s : Finset A) : (PMF.uniformOfFintype (A↪V)).toOuterMeasure (E s)≤
      ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m := by
    by_cases hs : s.card=m
    · simpa only [E,hs,true_and] using uniform_positions_bad (A:=A) B s
    · have he : E s=∅ := by ext f; simp [E,hs]
      rw [he]; simp
  calc
    _ ≤ (PMF.uniformOfFintype (A↪V)).toOuterMeasure (⋃s,E s) := measure_mono hsub
    _ ≤ ∑s : Finset A,(PMF.uniformOfFintype (A↪V)).toOuterMeasure (E s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑_s : Finset A,ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m :=
      Finset.sum_le_sum (fun s _ ↦ hE s)
    _ = _ := by simp [nsmul_eq_mul,Fintype.card_finset]

lemma uniform_half_bad {V : Type*} [Fintype V] [Nonempty V] (m : ℕ)
    [Nonempty (Fin (2*m)↪V)] (B : Set V)
    (hB : (Nat.card B:ℝ)≤(Fintype.card V:ℝ)/10) :
    (PMF.uniformOfFintype (Fin (2*m)↪V)).toOuterMeasure
      {f | m≤(Finset.univ.filter (fun a ↦ f a∈B)).card}≤(2/5:ℝ≥0∞)^m := by
  have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hb : (Nat.card B:ℝ)/(Fintype.card V:ℝ)≤(1/10:ℝ) := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hb' : ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))≤(1/10:ℝ≥0∞) := by
    have he : ENNReal.ofReal (1/10:ℝ)=(1/10:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq he
  calc
    _ ≤ (2:ℝ≥0∞)^(2*m)*ENNReal.ofReal ((Nat.card B:ℝ)/(Fintype.card V:ℝ))^m := by
      simpa using uniform_bad_count (A:=Fin (2*m)) B m
    _ ≤ (2:ℝ≥0∞)^(2*m)*(1/10:ℝ≥0∞)^m := mul_le_mul_right (pow_le_pow_left' hb' m) _
    _ = _ := by
      rw [pow_mul,←mul_pow]
      congr 1
      have h1 : (1/10:ℝ≥0∞)=ENNReal.ofReal (1/10:ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      have h2 : (2/5:ℝ≥0∞)=ENNReal.ofReal (2/5:ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      rw [h1,h2,show (2:ℝ≥0∞)^2=ENNReal.ofReal (4:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
      congr 1
      norm_num

end HardSphere.Sampling

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Index
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma coordinate_preserving (i : Index) :
    MeasurePreserving (fun ω : Noise ↦ ω i) law (gaussianReal 0 1) :=
  measurePreserving_eval_infinitePi _ _

lemma tent_nonneg (n : ℕ) (k : Fin (2 ^ n)) (t : ℝ) : 0 ≤ tent n k t :=
  le_max_left _ _

lemma tent_le_one (n : ℕ) (k : Fin (2 ^ n)) (t : ℝ) : tent n k t ≤ 1 := by
  unfold tent
  exact max_le (by norm_num) (by linarith [abs_nonneg ((2:ℝ)^(n+1)*t-(2*(k:ℝ)+1))])

lemma tent_positive_unique (n : ℕ) (k l : Fin (2 ^ n)) (t : ℝ)
    (hk : 0 < tent n k t) (hl : 0 < tent n l t) : k = l := by
  have hk' : |(2 : ℝ) ^ (n + 1) * t - (2 * (k : ℝ) + 1)| < 1 := by
    simpa only [tent, lt_max_iff, lt_self_iff_false, false_or, sub_pos] using hk
  have hl' : |(2 : ℝ) ^ (n + 1) * t - (2 * (l : ℝ) + 1)| < 1 := by
    simpa only [tent, lt_max_iff, lt_self_iff_false, false_or, sub_pos] using hl
  obtain ⟨hk1, hk2⟩ := abs_lt.mp hk'
  obtain ⟨hl1, hl2⟩ := abs_lt.mp hl'
  have hkl : (k : ℝ) < (l : ℝ) + 1 := by linarith
  have hlk : (l : ℝ) < (k : ℝ) + 1 := by linarith
  have hkl' : k.val < l.val + 1 := by exact_mod_cast hkl
  have hlk' : l.val < k.val + 1 := by exact_mod_cast hlk
  apply Fin.ext
  omega

lemma sum_tent_le_one (n : ℕ) (t : ℝ) : ∑ k, tent n k t ≤ 1 := by
  classical
  by_cases h : ∃ k, 0 < tent n k t
  · obtain ⟨k, hk⟩ := h
    rw [Finset.sum_eq_single k]
    · exact tent_le_one n k t
    · intro l _ hl
      exact le_antisymm (le_of_not_gt fun hp ↦ hl (tent_positive_unique n l k t hp hk))
        (tent_nonneg n l t)
    · simp
  · have hz : ∀ k, tent n k t = 0 := fun k ↦
      le_antisymm (le_of_not_gt fun hk ↦ h ⟨k, hk⟩) (tent_nonneg n k t)
    simp [hz]

lemma amplitude_nonneg (n : ℕ) : 0 ≤ amplitude n := by unfold amplitude; positivity

lemma norm_level_le (n : ℕ) (ω : Noise) {M : ℝ} (hM : 0 ≤ M)
    (hω : ∀ k : Fin (2 ^ n), |ω (.inr ⟨n, k⟩)| ≤ M) :
    ‖level n ω‖ ≤ amplitude n * M := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (amplitude_nonneg n) hM)).2
  intro t
  simp only [level, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    smul_eq_mul, tentMap, ContinuousMap.coe_mk, Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (amplitude_nonneg n)]
  apply mul_le_mul_of_nonneg_left _ (amplitude_nonneg n)
  calc
    |∑ k, ω (.inr ⟨n, k⟩) * tent n k t| ≤
        ∑ k, |ω (.inr ⟨n, k⟩) * tent n k t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |ω (.inr ⟨n, k⟩)| * tent n k t := by
      simp_rw [abs_mul, abs_of_nonneg (tent_nonneg n _ t)]
    _ ≤ ∑ k, M * tent n k t := Finset.sum_le_sum fun k _ ↦
      mul_le_mul_of_nonneg_right (hω k) (tent_nonneg n k t)
    _ = M * ∑ k, tent n k t := (Finset.mul_sum ..).symm
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (sum_tent_le_one n t) hM
    _ = M := mul_one _

lemma moment_ne_top : moment ≠ ∞ := by
  exact ENNReal.pow_ne_top (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num)).2.ne

lemma coordinate_tail (i : Index) {a : ℝ} (ha : 0 < a) :
    law {ω | a ≤ |ω i|} ≤ (ENNReal.ofReal a)⁻¹ ^ (4 : ℕ) * moment := by
  have hm := (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num))
  have he : eLpNorm (fun ω : Noise ↦ ω i) 4 law =
      eLpNorm (id : ℝ → ℝ) 4 (gaussianReal 0 1) :=
    by simpa only [Function.comp_def, id_eq] using
      (eLpNorm_comp_measurePreserving (p := 4) (g := (id : ℝ → ℝ))
        hm.aestronglyMeasurable (coordinate_preserving i))
  have ht := meas_ge_le_mul_pow_eLpNorm_enorm law (p := 4) (by norm_num) (by norm_num)
    (f := fun ω : Noise ↦ ω i)
    ((coordinate_preserving i).measurable.aestronglyMeasurable)
    (ε := ENNReal.ofReal a) (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) (fun h => absurd h (by simp))
  have hs : {ω : Noise | ENNReal.ofReal a ≤ ‖ω i‖ₑ} = {ω | a ≤ |ω i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  simpa only [Function.comp_def, id_eq, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast,
    Nat.cast_ofNat, he, hs, moment] using ht

lemma badLevel_bound (n : ℕ) :
    law (badLevel n) ≤ (ENNReal.ofReal (81/128 : ℝ)) ^ n * moment := by
  have hu : badLevel n = ⋃ k : Fin (2 ^ n), {ω | (4/3 : ℝ)^n ≤ |ω (.inr ⟨n, k⟩)|} := by
    ext ω; simp [badLevel]
  rw [hu]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ ≤ ∑ _k : Fin (2 ^ n), (ENNReal.ofReal ((4/3 : ℝ)^n))⁻¹ ^ (4 : ℕ) * moment :=
      Finset.sum_le_sum fun k _ ↦ coordinate_tail _ (by positivity)
    _ = (ENNReal.ofReal (81/128 : ℝ))^n * moment := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4/3),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3), ENNReal.ofReal_ofNat,
        ← mul_assoc]
      rw [ENNReal.inv_pow, ← pow_mul, Nat.mul_comm n 4, pow_mul, ← mul_pow]
      have hq : (2 : ℝ≥0∞) * (4/3)⁻¹ ^ (4 : ℕ) = ENNReal.ofReal (81/128 : ℝ) := by
        have hreal : (2 : ℝ) * (4/3)⁻¹ ^ (4 : ℕ) = 81/128 := by norm_num
        rw [← hreal, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      rw [hq]

lemma ae_eventually_coordinates_small : ∀ᵐ ω ∂law, ∀ᶠ n in atTop,
    ∀ k : Fin (2 ^ n), |ω (.inr ⟨n, k⟩)| < (4/3 : ℝ)^n := by
  have hs : (∑' n, law (badLevel n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum badLevel_bound)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    apply ENNReal.mul_ne_top _ moment_ne_top
    simpa only [ENNReal.inv_ne_top] using
      (ne_of_gt (tsub_pos_of_lt (by rw [ENNReal.ofReal_lt_one]; norm_num : (ENNReal.ofReal (81/128 : ℝ)) < 1)))
  filter_upwards [ae_eventually_notMem hs] with ω hω
  filter_upwards [hω] with n hn
  simpa only [badLevel, Set.mem_ofPred_eq, not_exists, not_le] using hn

lemma decay_lt_one : (4/3 : ℝ) / Real.sqrt 2 < 1 := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_one hp]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma summable_level_bound : Summable (fun n : ℕ ↦ amplitude n * (4/3 : ℝ)^n) := by
  have h := (summable_geometric_of_lt_one (by positivity : 0 ≤ (4/3 : ℝ) / Real.sqrt 2)
    decay_lt_one).mul_left (1/2 : ℝ)
  have heq : (fun n : ℕ ↦ amplitude n * (4/3 : ℝ)^n) =
      (fun n : ℕ ↦ (1/2 : ℝ) * ((4/3 : ℝ) / Real.sqrt 2)^n) := by
    funext n
    simp only [amplitude, div_eq_mul_inv, mul_pow]
    ring
  rw [heq]
  exact h

lemma ae_summable_level : ∀ᵐ ω ∂law, Summable (fun n ↦ level n ω) := by
  filter_upwards [ae_eventually_coordinates_small] with ω hω
  apply summable_level_bound.of_norm_bounded_eventually_nat
  filter_upwards [hω] with n hn
  exact norm_level_le n ω (by positivity) (fun k ↦ (hn k).le)

open Complex in
lemma hasLaw_gaussian_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {m : ℕ → ℝ} {v : ℕ → ℝ≥0} {m₀ : ℝ} {v₀ : ℝ≥0}
    (hX : ∀ n, HasLaw (X n) (gaussianReal (m n) (v n)) P)
    (hY : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)))
    (hm : Tendsto m atTop (𝓝 m₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    HasLaw Y (gaussianReal m₀ v₀) P := by
  have hmY := aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ (hX n).aemeasurable) hY
  refine ⟨hmY, Measure.ext_of_charFun (funext fun t ↦ ?_)⟩
  have : IsProbabilityMeasure (P.map Y) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hlim : Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (P.map Y) t)) := by
    have he (Z : Ω → ℝ) (hZ : AEMeasurable Z P) :
        charFun (P.map Z) t = ∫ ω, exp ((t * Z ω : ℝ) * I) ∂P := by
      rw [charFun_apply_real, integral_map hZ (by fun_prop)]
      simp only [ofReal_mul]
    simp_rw [he _ (hX _).aemeasurable, he _ hmY]
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro n
      exact ((by fun_prop : Continuous (fun x : ℝ ↦ exp ((t * x : ℝ) * I))).measurable.comp_aemeasurable
        (hX n).aemeasurable).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact ae_of_all P fun ω ↦ le_of_eq (norm_exp_ofReal_mul_I _)
    · filter_upwards [hY] with ω hω
      exact continuous_exp.continuousAt.tendsto.comp
        ((continuous_ofReal.tendsto _ |>.comp (tendsto_const_nhds.mul hω)).mul_const I)
  have hlim' : Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (gaussianReal m₀ v₀) t)) := by
    simp_rw [(hX _).map_eq, charFun_gaussianReal]
    exact continuous_exp.continuousAt.tendsto.comp
      (((tendsto_const_nhds.mul (continuous_ofReal.tendsto _ |>.comp hm)).mul_const I).sub
        (((continuous_ofReal.tendsto _ |>.comp (NNReal.continuous_coe.tendsto _ |>.comp hv)).mul_const
          ((t : ℂ)^2)).div_const 2))
  exact tendsto_nhds_unique hlim hlim'

lemma hasLaw_centered_gaussian_sum {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P) (hind : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) (gaussianReal 0 (∑ i, v i)) P := by
  classical
  have hg := hind.hasGaussianLaw_fun_sum (fun i ↦ (hX i).hasGaussianLaw)
  have hmean : ∫ ω, ∑ i, X i ω ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ ↦ (hX i).hasGaussianLaw.integrable)]
    simp only [(hX _).integral_eq, integral_id_gaussianReal, Finset.sum_const_zero]
  have hvar : Var[fun ω ↦ ∑ i, X i ω; P] = ∑ i, (v i : ℝ) := by
    have hh := IndepFun.variance_sum (s := Finset.univ)
      (fun i _ ↦ (hX i).hasGaussianLaw.memLp_two)
      (fun i _ j _ hij ↦ hind.indepFun hij)
    have he : (fun ω ↦ ∑ i, X i ω) = ∑ i, X i := by funext ω; simp
    rw [he]
    simpa only [(hX _).variance_eq, variance_id_gaussianReal] using hh
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, hmean, hvar]
  simp only [← NNReal.coe_sum, Real.toNNReal_coe]

lemma sum_split_level (n : ℕ) (f : Fin (2^(n+1)) → ℝ) :
    ∑ k, f k = ∑ k, f (leftIndex n k) + ∑ k, f (rightIndex n k) := by
  let e : Fin (2^n + 2^n) ≃ Fin (2^(n+1)) :=
    finCongr (by simp [pow_succ, Nat.mul_two])
  rw [← Equiv.sum_comp e, Fin.sum_univ_add]
  rfl

lemma tent_left (n : ℕ) (k : Fin (2^n)) (s : ℝ) :
    tent (n+1) (leftIndex n k) s = tent n k (2*s) := by
  unfold tent leftIndex
  congr 3
  simp only [pow_succ]
  ring

lemma tent_right (n : ℕ) (k : Fin (2^n)) (s : ℝ) :
    tent (n+1) (rightIndex n k) s = tent n k (2*s-1) := by
  unfold tent rightIndex
  congr 3
  simp only [pow_succ, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  ring

lemma tent_nonpos (n : ℕ) (k : Fin (2^n)) {s : ℝ} (hs : s ≤ 0) : tent n k s = 0 := by
  unfold tent
  apply max_eq_left
  have hpow : 0 ≤ (2:ℝ)^(n+1) := by positivity
  have hx : (2:ℝ)^(n+1)*s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpow hs
  rw [abs_of_nonpos (by linarith [show (0:ℝ) ≤ k by positivity])]
  linarith [show (0:ℝ) ≤ k by positivity]

lemma tent_ge_one (n : ℕ) (k : Fin (2^n)) {s : ℝ} (hs : 1 ≤ s) : tent n k s = 0 := by
  have hk : (k : ℝ) + 1 ≤ (2:ℝ)^n := by exact_mod_cast k.isLt
  have hp : 0 < (2:ℝ)^n := by positivity
  have hx : (2:ℝ)^n*2 ≤ (2:ℝ)^n*2*s := le_mul_of_one_le_right (by positivity) hs
  unfold tent
  simp only [pow_succ]
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (2:ℝ)^n*2*s-(2*(k:ℝ)+1))]
  exact max_eq_left (by linarith)

lemma hatKernel_rec (n : ℕ) (s t : ℝ) :
    hatKernel (n+1) s t = hatKernel n (2*s) (2*t) + hatKernel n (2*s-1) (2*t-1) := by
  unfold hatKernel
  rw [sum_split_level]
  simp only [tent_left, tent_right]

lemma partialBridge_zero_left (n : ℕ) {s : ℝ} (hs : s ≤ 0 ∨ 1 ≤ s) (t : ℝ) :
    partialBridge n s t = 0 := by
  rcases hs with hs | hs <;> simp [partialBridge, hatKernel, tent_nonpos, tent_ge_one, hs]

lemma partialBridge_zero_right (n : ℕ) (s : ℝ) {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) :
    partialBridge n s t = 0 := by
  rcases ht with ht | ht <;> simp [partialBridge, hatKernel, tent_nonpos, tent_ge_one, ht]

lemma partialBridge_rec (n : ℕ) (s t : ℝ) :
    partialBridge (n+1) s t = (1/4 : ℝ) * tent 0 0 s * tent 0 0 t +
      (1/2 : ℝ)*(partialBridge n (2*s) (2*t) + partialBridge n (2*s-1) (2*t-1)) := by
  have h0 : hatKernel 0 s t = tent 0 0 s * tent 0 0 t := by
    simp [hatKernel]
  have hx : ∑ m ∈ Finset.range n, weight (m+1)*hatKernel (m+1) s t =
      (1/2 : ℝ)*(partialBridge n (2*s) (2*t) + partialBridge n (2*s-1) (2*t-1)) := by
    simp only [partialBridge, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [hatKernel_rec]
    simp only [weight, pow_succ]
    ring
  change (∑ m ∈ Finset.range (n+1), weight m * hatKernel m s t) = _
  rw [Finset.sum_range_succ', hx, h0]
  simp only [weight, pow_zero, mul_one]
  ring

lemma tent_zero_left {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1/2) : tent 0 0 s = 2*s := by
  simp only [tent, pow_one, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  ring

lemma tent_zero_right {s : ℝ} (h0 : 1/2 ≤ s) (h1 : s ≤ 1) : tent 0 0 s = 2*(1-s) := by
  simp only [tent, pow_one, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

lemma weight_step (n : ℕ) : weight (n+1) = (1/2 : ℝ)*weight n := by
  simp only [weight, pow_succ]
  ring

lemma abs_half_mul (x : ℝ) : |(1/2 : ℝ)*x| = (1/2 : ℝ)*|x| := by
  rw [abs_mul]
  norm_num

lemma partialBridge_error_ordered (n : ℕ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : t ≤ 1) (hst : s ≤ t) :
    |partialBridge n s t - (s-s*t)| ≤ weight n := by
  induction n generalizing s t with
  | zero =>
      have hnn : 0 ≤ s-s*t := by nlinarith
      have hb : s-s*t ≤ (1/4 : ℝ) := by nlinarith [sq_nonneg (s-1/2)]
      simp only [partialBridge, Finset.range_zero, Finset.sum_empty, zero_sub,
        abs_neg, abs_of_nonneg hnn, weight, pow_zero, mul_one]
      exact hb
  | succ n ih =>
      rw [partialBridge_rec, weight_step]
      by_cases ht2 : t ≤ 1/2
      · have hs2 : s ≤ 1/2 := hst.trans ht2
        rw [tent_zero_left hs hs2, tent_zero_left (hs.trans hst) ht2,
          partialBridge_zero_left n (Or.inl (by linarith : 2*s-1 ≤ 0)), add_zero]
        have hh := ih (s := 2*s) (t := 2*t) (by linarith) (by linarith) (by linarith)
        calc
          _ = (1/2 : ℝ)*|partialBridge n (2*s) (2*t) - (2*s-(2*s)*(2*t))| := by
            rw [← abs_half_mul]
            congr 1
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
      · by_cases hs2 : 1/2 ≤ s
        · rw [tent_zero_right hs2 (hst.trans ht), tent_zero_right (hs2.trans hst) ht,
            partialBridge_zero_left n (Or.inr (by linarith : 1 ≤ 2*s)), zero_add]
          have hh := ih (s := 2*s-1) (t := 2*t-1) (by linarith) (by linarith) (by linarith)
          calc
            _ = (1/2 : ℝ)*|partialBridge n (2*s-1) (2*t-1) - ((2*s-1)-(2*s-1)*(2*t-1))| := by
              rw [← abs_half_mul]
              congr 1
              ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
        · rw [tent_zero_left hs (by linarith), tent_zero_right (by linarith) ht,
            partialBridge_zero_right n _ (Or.inr (by linarith : 1 ≤ 2*t)),
            partialBridge_zero_left n (Or.inl (by linarith : 2*s-1 ≤ 0))]
          have he : (1/4 : ℝ)*(2*s)*(2*(1-t)) + (1/2)*(0+0) - (s-s*t) = 0 := by ring
          rw [he, abs_zero]
          unfold weight
          positivity

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PartialIndex
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma partialBridge_symm (n : ℕ) (s t : ℝ) : partialBridge n s t = partialBridge n t s := by
  simp only [partialBridge, hatKernel, mul_comm (tent _ _ s) (tent _ _ t)]

lemma partialBridge_error (n : ℕ) {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |partialBridge n s t - (min s t-s*t)| ≤ weight n := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact partialBridge_error_ordered n hs.1 ht.2 hst
  · rw [partialBridge_symm, min_eq_right hts, mul_comm s t]
    exact partialBridge_error_ordered n ht.1 hs.2 hts

lemma partialBridge_tendsto {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Filter.Tendsto (fun n ↦ partialBridge n s t) Filter.atTop (𝓝 (min s t-s*t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ partialBridge_error n hs ht)
  change Filter.Tendsto (fun n ↦ weight n) Filter.atTop (𝓝 0)
  simpa only [weight, mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)) :
      Filter.Tendsto (fun n ↦ (1/4:ℝ)*(1/2:ℝ)^n) Filter.atTop (𝓝 ((1/4:ℝ)*0)))

lemma partialEmbed_injective (n : ℕ) : Function.Injective (partialEmbed n) := by
  intro i j hij
  cases i with
  | inl u =>
    cases j with
    | inl v => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr j => cases hij
  | inr i =>
    cases j with
    | inl u => cases hij
    | inr j =>
      obtain ⟨m,k⟩ := i
      obtain ⟨l,q⟩ := j
      simp only [partialEmbed, Sum.inr.injEq] at hij
      cases m; cases l
      cases hij
      rfl

lemma partialPath_expansion (n : ℕ) (t : Time) (ω : Noise) :
    partialPath n ω t = ∑ i : PartialIndex n, coefficient n t i * ω (partialEmbed n i) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coefficient, partialEmbed,
    Fintype.sum_unique, partialPath, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul, ContinuousMap.sum_apply, level, tentMap,
    ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m),
    amplitude m * tent m k t * ω (.inr ⟨m,k⟩)) n]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma coefficient_covariance (n : ℕ) (s t : ℝ) :
    ∑ i : PartialIndex n, coefficient n s i * coefficient n t i =
      s*t + partialBridge n s t := by
  have hamp (m : ℕ) : amplitude m ^ 2 = weight m := by
    have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    simp only [amplitude, mul_pow, weight]
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, inv_pow, hs]
    norm_num
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coefficient, Fintype.sum_unique]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m),
    amplitude m * tent m k s * (amplitude m * tent m k t)) n]
  congr 1
  unfold partialBridge
  apply Finset.sum_congr rfl
  intro m _
  rw [hatKernel, Finset.mul_sum, ← hamp]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma independent_coordinates : iIndepFun (fun i ω ↦ ω i) law :=
  iIndepFun_infinitePi (fun _ ↦ measurable_id)

lemma finite_coordinate_law (n : ℕ) (c : PartialIndex n → ℝ) :
    HasLaw (fun ω ↦ ∑ i, c i * ω (partialEmbed n i))
      (gaussianReal 0 (∑ i, NNReal.mk ((c i)^2) (sq_nonneg _))) law := by
  have hh (i : PartialIndex n) : HasLaw (fun ω ↦ c i * ω (partialEmbed n i))
      (gaussianReal 0 (NNReal.mk ((c i)^2) (sq_nonneg _))) law := by
    simpa only [mul_zero, mul_one] using
      gaussianReal_const_mul (coordinate_preserving (partialEmbed n i)).hasLaw (c i)
  exact hasLaw_centered_gaussian_sum hh
    ((independent_coordinates.precomp (partialEmbed_injective n)).comp
      (fun i x ↦ c i*x) (fun i ↦ by fun_prop))

lemma square_sum_covariance {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (f : ι → κ → ℝ) :
    ∑ u, (∑ i, c i*f i u)^2 = ∑ i, ∑ j, c i*c j*(∑ u, f i u*f j u) := by
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma ae_partialPath_tendsto : ∀ᵐ ω ∂law,
    Tendsto (fun n ↦ partialPath n ω) atTop (𝓝 (path ω)) := by
  filter_upwards [ae_summable_level] with ω hω
  exact tendsto_const_nhds.add hω.hasSum.tendsto_sum_nat

lemma finite_projection_expansion {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) (ω : Noise) :
    ∑ i, c i * partialPath n ω (t i) =
      ∑ u : PartialIndex n, (∑ i, c i * coefficient n (t i) u) * ω (partialEmbed n u) := by
  simp_rw [partialPath_expansion, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finite_projection_variance {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) :
    ∑ u : PartialIndex n, (∑ i, c i * coefficient n (t i) u)^2 =
      ∑ i, ∑ j, c i*c j*((t i : ℝ)*(t j : ℝ)+partialBridge n (t i) (t j)) := by
  rw [square_sum_covariance]
  simp_rw [coefficient_covariance]

lemma finite_projection_law {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * partialPath n ω (t i))
      (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i*c j*((t i : ℝ)*(t j : ℝ)+partialBridge n (t i) (t j))))) law := by
  have hh := finite_coordinate_law n (fun u ↦ ∑ i, c i * coefficient n (t i) u)
  simp_rw [finite_projection_expansion]
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  rw [← finite_projection_variance]
  change Real.toNNReal (∑ u : PartialIndex n,
    ((NNReal.mk ((∑ i, c i * coefficient n (t i) u)^2) (sq_nonneg _) : ℝ≥0) : ℝ)) = _
  rw [← NNReal.coe_sum, Real.toNNReal_coe]

lemma path_projection_law {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * path ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*min (t i : ℝ) (t j : ℝ)))) law := by
  refine hasLaw_gaussian_of_ae_tendsto (fun n ↦ finite_projection_law n c t) ?_
    tendsto_const_nhds ?_
  · filter_upwards [ae_partialPath_tendsto] with ω hω
    apply tendsto_finsetSum
    intro i _
    exact tendsto_const_nhds.mul ((continuous_eval_const (t i)).tendsto _ |>.comp hω)
  · apply continuous_real_toNNReal.tendsto _ |>.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    have hh := ((tendsto_const_nhds (x := (t i : ℝ)*(t j : ℝ))).add
      (partialBridge_tendsto (t i).property (t j).property)).const_mul (c i*c j)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

lemma finite_linear_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finite_path_gaussian {ι : Type*} [Fintype ι] (t : ι → Time) :
    HasGaussianLaw (fun ω i ↦ path ω (t i)) law := by
  classical
  have hm : Measurable (fun ω i ↦ path ω (t i)) :=
    Measurable.of_eval fun coordinate ↦
      (continuous_eval_const (t coordinate)).measurable.comp measurable_path
  refine ⟨?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  refine ⟨0, Real.toNNReal (∑ i, ∑ j,
    L (Pi.single i 1)*L (Pi.single j 1)*min (t i : ℝ) (t j : ℝ)), ?_⟩
  rw [Measure.map_map L.continuous.measurable hm]
  convert (path_projection_law (fun i ↦ L (Pi.single i 1)) t).map_eq using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  exact finite_linear_projection L _

lemma path_eval_law (t : Time) :
    HasLaw (fun ω ↦ path ω t) (gaussianReal 0 (Real.toNNReal t.val)) law := by
  simpa using path_projection_law (fun _ : Unit ↦ (1:ℝ)) (fun _ ↦ t)

lemma path_variance (t : Time) : Var[fun ω ↦ path ω t; law] = t.val := by
  rw [(path_eval_law t).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ t.property.1]

lemma path_add_law (s t : Time) :
    HasLaw (fun ω ↦ path ω s + path ω t)
      (gaussianReal 0 ((s:ℝ)+(t:ℝ)+2*min (s:ℝ) (t:ℝ)).toNNReal) law := by
  have hh := path_projection_law (fun _ : Bool ↦ (1:ℝ)) (fun b ↦ if b then s else t)
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul, min_self] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1
  rw [min_comm (t:ℝ) (s:ℝ)]
  ring

lemma path_covariance (s t : Time) :
    cov[fun ω ↦ path ω s, fun ω ↦ path ω t; law] = min (s:ℝ) (t:ℝ) := by
  have hs : 0 ≤ (s:ℝ) := s.property.1
  have ht : 0 ≤ (t:ℝ) := t.property.1
  have hmin : 0 ≤ min (s:ℝ) (t:ℝ) := le_min hs ht
  have hvar := variance_fun_add (path_eval_law s).hasGaussianLaw.memLp_two
    (path_eval_law t).hasGaussianLaw.memLp_two
  rw [path_variance s, path_variance t, (path_add_law s t).variance_eq,
    variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity)] at hvar
  linarith

lemma denseEval_embedding : MeasurableEmbedding denseEval := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval fun _ ↦ (continuous_eval_const _).measurable
  · intro f g h
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq Time).equalizer f.continuous g.continuous h

lemma continuous_path_law_ext {X Y : Noise → C(Time,ℝ)}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ) (t : ι → Time),
      law.map (fun ω ↦ ∑ i, c i * X ω (t i)) =
        law.map (fun ω ↦ ∑ i, c i * Y ω (t i))) :
    law.map X = law.map Y := by
  apply denseEval_embedding.map_injective
  rw [Measure.map_map denseEval_embedding.measurable hX,
    Measure.map_map denseEval_embedding.measurable hY]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (denseEval_embedding.measurable.comp hX).aemeasurable
    (denseEval_embedding.measurable.comp hY).aemeasurable).mpr
  intro I
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  congr 1
  have hXm : Measurable (fun ω ↦ I.restrict (fun x ↦ denseEval (X ω) x)) :=
    Measurable.of_eval fun coordinate ↦ (measurable_pi_apply coordinate.val).comp
      (denseEval_embedding.measurable.comp hX)
  have hYm : Measurable (fun ω ↦ I.restrict (fun x ↦ denseEval (Y ω) x)) :=
    Measurable.of_eval fun coordinate ↦ (measurable_pi_apply coordinate.val).comp
      (denseEval_embedding.measurable.comp hY)
  simp only [Function.comp_def, Finset.restrict_def] at hXm hYm ⊢
  rw [Measure.map_map L.continuous.measurable hXm,
    Measure.map_map L.continuous.measurable hYm]
  convert h (fun i : I ↦ L (Pi.single i 1))
    (fun i : I ↦ TopologicalSpace.denseSeq Time i.val) using 1 <;>
    congr 1 <;> funext ω <;> exact finite_linear_projection L _

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PrefixMap
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma prefixTime_le (u t : Time) : (prefixTime u t:ℝ) ≤ u := by
  change (u:ℝ)*(t:ℝ) ≤ u
  nlinarith [u.property.1,t.property.2]
lemma le_suffixTime (u t : Time) : (u:ℝ) ≤ suffixTime u t := by
  change (u:ℝ) ≤ (u:ℝ)+(1-(u:ℝ))*(t:ℝ)
  nlinarith [u.property.2,t.property.1]

lemma split_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun t ω ↦ prefixMap u (path ω) t)
      (fun t ω ↦ suffixMap u (path ω) t)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u
    (fun j ↦ j.val.elim (prefixTime u) (suffixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ match i.val with
      | .inl _ => ev (some i)
      | .inr _ => ev (some i) - ev none)
  convert! (finite_path_gaussian loc).map_fun L using 1
  all_goals try with_reducible_and_instances rfl
  funext ω i
  cases hi : i.val <;> simp [L,loc,hi,ev]

lemma independent_split (u : Time) :
    IndepFun (fun ω ↦ prefixMap u (path ω)) (fun ω ↦ suffixMap u (path ω)) law := by
  have hc (s t : Time) :
      cov[fun ω ↦ prefixMap u (path ω) s, fun ω ↦ suffixMap u (path ω) t; law] = 0 := by
    simp only [prefixMap_apply,suffixMap_apply]
    rw [covariance_fun_sub_right
      (path_eval_law _).hasGaussianLaw.memLp_two
      (path_eval_law _).hasGaussianLaw.memLp_two
      (path_eval_law _).hasGaussianLaw.memLp_two,
      path_covariance,path_covariance,
      min_eq_left ((prefixTime_le u s).trans (le_suffixTime u t)),
      min_eq_left (prefixTime_le u s),sub_self]
  have hi := (split_gaussian u).indepFun_of_covariance_eq_zero
    (fun t ↦ ((continuous_eval_const t).measurable.comp
      ((prefixMap u).continuous.measurable.comp measurable_path)).aemeasurable)
    (fun t ↦ ((continuous_eval_const t).measurable.comp
      ((suffixMap u).continuous.measurable.comp measurable_path)).aemeasurable) hc
  have hid := hi.comp
    (Measurable.of_eval fun index ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time index))
    (Measurable.of_eval fun index ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time index))
  have hh := hid.comp denseEval_embedding.measurable_invFun denseEval_embedding.measurable_invFun
  convert hh using 1 <;> funext ω <;>
    exact (denseEval_embedding.leftInverse_invFun _).symm

lemma scaled_path_projection_law {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * (Real.sqrt r • path ω) (t i))
      (gaussianReal 0 (Real.toNNReal (r * ∑ i, ∑ j,
        c i*c j*min (t i:ℝ) (t j:ℝ)))) law := by
  have hh := path_projection_law (fun i ↦ c i * Real.sqrt r) t
  convert hh using 1
  · funext ω
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    ring
  · congr 1
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      r * (c i*c j*min (t i:ℝ) (t j:ℝ)) =
          Real.sqrt r ^ 2 * (c i*c j*min (t i:ℝ) (t j:ℝ)) := by rw [Real.sq_sqrt hr]
      _ = _ := by ring

lemma prefix_law (u : Time) :
    law.map (fun ω ↦ prefixMap u (path ω)) =
      law.map (fun ω ↦ Real.sqrt (u:ℝ) • path ω) := by
  apply continuous_path_law_ext (X := fun ω ↦ prefixMap u (path ω))
    (Y := fun ω ↦ Real.sqrt (u:ℝ) • path ω)
    ((prefixMap u).continuous.measurable.comp measurable_path)
    ((show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (u:ℝ) • f) from
      (by fun_prop)).comp measurable_path)
  intro ι _ c t
  have h := path_projection_law c (fun i ↦ prefixTime u (t i))
  have hvar : (∑ i, ∑ j, c i*c j*min (prefixTime u (t i):ℝ) (prefixTime u (t j):ℝ)) =
      (u:ℝ)*∑ i, ∑ j, c i*c j*min (t i:ℝ) (t j:ℝ) := by
    simp only [prefixTime,ContinuousMap.coe_mk]
    simp_rw [← mul_min_of_nonneg _ _ u.property.1]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hvar] at h
  exact h.map_eq.trans (scaled_path_projection_law _ u.property.1 c t).map_eq.symm

lemma suffix_projection_algebra {ι : Type*} [Fintype ι]
    (u : Time) (c : ι → ℝ) (t : ι → Time) :
    let a : Option ι → ℝ := fun i ↦ i.elim (-∑ i, c i) c
    let v : Option ι → Time := fun i ↦ i.elim u (fun j ↦ suffixTime u (t j))
    (∑ i, ∑ j, a i*a j*min (v i:ℝ) (v j:ℝ)) =
      (1-(u:ℝ))*∑ i, ∑ j, c i*c j*min (t i:ℝ) (t j:ℝ) := by
  let A : ℝ := ∑ i, c i
  have hh : (∑ i, ∑ j, c i*c j*(u:ℝ)) = A*A*(u:ℝ) := by
    dsimp only [A]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  have h1 : (∑ i, (-A)*c i*(u:ℝ)) = -A*A*(u:ℝ) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h2 : (∑ i, c i*(-A)*(u:ℝ)) = -A*A*(u:ℝ) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    dsimp only [A]
    ring
  have h3 : (∑ i, ∑ j, c i*c j*((1-(u:ℝ))*min (t i:ℝ) (t j:ℝ))) =
      (1-(u:ℝ))*∑ i, ∑ j, c i*c j*min (t i:ℝ) (t j:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only
  simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,
    min_self,min_eq_left (le_suffixTime u (t _)),min_eq_right (le_suffixTime u (t _))]
  have ht i j : min (suffixTime u (t i):ℝ) (suffixTime u (t j):ℝ) =
      (u:ℝ)+(1-(u:ℝ))*min (t i:ℝ) (t j:ℝ) := by
    change min ((u:ℝ)+(1-(u:ℝ))*(t i:ℝ)) ((u:ℝ)+(1-(u:ℝ))*(t j:ℝ)) = _
    rw [min_add_add_left,← mul_min_of_nonneg _ _ (sub_nonneg.mpr u.property.2)]
  simp_rw [ht,mul_add,Finset.sum_add_distrib]
  change (-A)*(-A)*(u:ℝ)+(∑ i,(-A)*c i*(u:ℝ))+
    ((∑ i,c i*(-A)*(u:ℝ))+((∑ i,∑ j,c i*c j*(u:ℝ))+_)) = _
  rw [hh,h1,h2,h3]
  ring

lemma suffix_law (u : Time) :
    law.map (fun ω ↦ suffixMap u (path ω)) =
      law.map (fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω) := by
  apply continuous_path_law_ext (X := fun ω ↦ suffixMap u (path ω))
    (Y := fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω)
    ((suffixMap u).continuous.measurable.comp measurable_path)
    ((show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (1-(u:ℝ)) • f) from
      (by fun_prop)).comp measurable_path)
  intro ι _ c t
  have hh := path_projection_law (fun i : Option ι ↦ i.elim (-∑ i,c i) c)
    (fun i ↦ i.elim u (fun j ↦ suffixTime u (t j)))
  rw [suffix_projection_algebra] at hh
  have heq : (fun ω ↦ ∑ i, c i*suffixMap u (path ω) (t i)) =
      (fun ω ↦ ∑ i : Option ι, i.elim (-∑ i,c i) c *
        path ω (i.elim u (fun j ↦ suffixTime u (t j)))) := by
    funext ω
    simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,suffixMap_apply,
      mul_sub,Finset.sum_sub_distrib,neg_mul,Finset.sum_mul]
    ring
  rw [heq, hh.map_eq,
    (scaled_path_projection_law _ (sub_nonneg.mpr u.property.2) c t).map_eq]

lemma split_path_law (u : Time) :
    law.map (fun ω ↦ (prefixMap u (path ω),suffixMap u (path ω))) =
      (wiener.map (fun f ↦ Real.sqrt (u:ℝ) • f)).prod
        (wiener.map (fun f ↦ Real.sqrt (1-(u:ℝ)) • f)) := by
  calc
    _ = (law.map (fun ω ↦ prefixMap u (path ω))).prod
        (law.map (fun ω ↦ suffixMap u (path ω))) := by
      simpa only [Function.comp_def] using (independent_split u).map_prod_eq_prod_map_map
        ((prefixMap u).continuous.measurable.comp measurable_path).aemeasurable
        ((suffixMap u).continuous.measurable.comp measurable_path).aemeasurable
    _ = _ := by
      rw [prefix_law,suffix_law]
      unfold wiener
      rw [Measure.map_map (show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (u:ℝ) • f) from by fun_prop) measurable_path,
        Measure.map_map (show Measurable (fun f : C(Time,ℝ) ↦ Real.sqrt (1-(u:ℝ)) • f) from by fun_prop) measurable_path]
      rfl

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_HilbertJet
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

attribute [local instance] scalarL2_addCommMonoid scalarL2_module scalarL2_completeSpace

lemma continuous_torusDistance (L : Length) : Continuous (fun p : Torus L × Torus L ↦ torusDistance L p.1 p.2) := by
  unfold torusDistance
  fun_prop

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_NormalizedPrefix
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
namespace Wiener

lemma normalized_split_preserving (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    MeasurePreserving (fun w : C(Time,ℝ) ↦ (normalizedPrefix u w,normalizedSuffix u w))
      wiener (wiener.prod wiener) := by
  have hm : Measurable (fun w : C(Time,ℝ) ↦ (prefixMap u w,suffixMap u w)) := by fun_prop
  have heq : wiener.map (fun w : C(Time,ℝ) ↦ (prefixMap u w,suffixMap u w)) =
      (wiener.map (fun f ↦ Real.sqrt (u:ℝ) • f)).prod
        (wiener.map (fun f ↦ Real.sqrt (1-(u:ℝ)) • f)) := by
    rw [wiener,Measure.map_map hm measurable_path]
    exact split_path_law u
  refine ⟨by fun_prop,?_⟩
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)] at heq
  have hh := congrArg (fun μ : Measure (C(Time,ℝ) × C(Time,ℝ)) ↦ μ.map
    (fun p ↦ ((Real.sqrt (u:ℝ))⁻¹ • p.1,(Real.sqrt (1-(u:ℝ)))⁻¹ • p.2))) heq
  rw [Measure.map_map (by fun_prop) hm, Measure.map_map (by fun_prop) (by fun_prop)] at hh
  simpa only [normalizedPrefix,normalizedSuffix,smul_apply,
    Function.comp_def,Prod.map,smul_smul,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hu)),
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hu'))),
    one_smul,Prod.mk.eta,Measure.map_id'] using hh

end Wiener

open Wiener

lemma splitTime_pos (s t : ℝ) (hs : 0 < s) (ht : 0<t) : 0<(splitTime s t hs ht:ℝ) :=
  div_pos hs (add_pos hs ht)

lemma splitTime_lt_one (s t : ℝ) (hs : 0 < s) (ht : 0<t) : (splitTime s t hs ht:ℝ)<1 :=
  (div_lt_one (add_pos hs ht)).mpr (by linarith)

lemma sqrt_split_left (s t : ℝ) (hs : 0 < s) (ht : 0<t) :
    Real.sqrt (2*s) * (Real.sqrt (splitTime s t hs ht:ℝ))⁻¹ = Real.sqrt (2*(s+t)) := by
  have h : Real.sqrt (2*(s+t)) * Real.sqrt (splitTime s t hs ht:ℝ) = Real.sqrt (2*s) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    change 2*(s+t)*(s/(s+t))=2*s
    field_simp
  rw [← h,mul_assoc,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (splitTime_pos s t hs ht))),mul_one]

lemma sqrt_split_right (s t : ℝ) (hs : 0 < s) (ht : 0<t) :
    Real.sqrt (2*t) * (Real.sqrt (1-(splitTime s t hs ht:ℝ)))⁻¹ = Real.sqrt (2*(s+t)) := by
  have h : Real.sqrt (2*(s+t)) * Real.sqrt (1-(splitTime s t hs ht:ℝ)) = Real.sqrt (2*t) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    change 2*(s+t)*(1-s/(s+t))=2*t
    field_simp
    ring
  rw [← h,mul_assoc,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (splitTime_lt_one s t hs ht)))),mul_one]

lemma configurationPrefix_continuous (N : ℕ) (L : Length) (u : Time) :
    Continuous (configurationPrefix N L u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath N L × Time ↦ p.1 (prefixTime u p.2))
  fun_prop

lemma configurationSuffix_continuous (N : ℕ) (L : Length) (u : Time) :
    Continuous (configurationSuffix N L u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ConfigurationPath N L × Time ↦ p.1 (suffixTime u p.2))
  fun_prop

lemma coordinateSplit_preserving (N : ℕ) (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    MeasurePreserving (fun w : CoordinatePaths N ↦
      (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)))
      (coordinateWiener N) ((coordinateWiener N).prod (coordinateWiener N)) := by
  have hm : Measurable (fun w : CoordinatePaths N ↦
      fun p ↦ (normalizedPrefix u (w p),normalizedSuffix u (w p))) := by fun_prop
  have h : MeasurePreserving (fun w : CoordinatePaths N ↦
      fun p ↦ (normalizedPrefix u (w p),normalizedSuffix u (w p)))
      (coordinateWiener N) (Measure.pi fun _ : Direction N ↦ wiener.prod wiener) := by
    refine ⟨hm,?_⟩
    unfold coordinateWiener
    rw [Measure.pi_map_pi (fun _ ↦ (normalized_split_preserving u hu hu').measurable.aemeasurable)]
    simp_rw [(normalized_split_preserving u hu hu').map_eq]
  exact (measurePreserving_arrowProdEquivProdArrow C(Time,ℝ) C(Time,ℝ) (Direction N)
    (fun _ ↦ wiener) (fun _ ↦ wiener)).comp h

lemma prefix_freeTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0 < s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    configurationPrefix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X) =
      freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X := by
  ext v i j
  change X i j + ((Real.sqrt (2*(s+t))*w (i,j) (prefixTime _ v):ℝ):AddCircle L.val)=
    X i j + ((Real.sqrt (2*s)*((Real.sqrt (_:ℝ))⁻¹*w (i,j) (prefixTime _ v)):ℝ):AddCircle L.val)
  rw [← mul_assoc,sqrt_split_left]

lemma suffix_freeTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0 < s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    configurationSuffix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X) =
      freeTrajectory N L t (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p))
        (freeTrajectory N L (s+t) w X (splitTime s t hs ht)) := by
  ext v i j
  change X i j + ((Real.sqrt (2*(s+t))*w (i,j) (suffixTime _ v):ℝ):AddCircle L.val)=
    (X i j + ((Real.sqrt (2*(s+t))*w (i,j) _ :ℝ):AddCircle L.val))+
      ((Real.sqrt (2*t)*((Real.sqrt (1-(_:ℝ)))⁻¹*(w (i,j) (suffixTime _ v)-w (i,j) _)):ℝ):AddCircle L.val)
  rw [← mul_assoc,sqrt_split_right,mul_sub,AddCircle.coe_sub]
  abel

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CenteredCircleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma torusDistance_triangle' (L : Length) (x y z : Torus L) :
    torusDistance L x z≤torusDistance L x y+torusDistance L y z := by
  simpa only [euclideanTorusPoint_dist] using dist_triangle
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L z)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathDiameter
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma intervalDiameter_nonneg {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) :
    0 ≤ intervalDiameter a b ω := norm_nonneg _

lemma intervalDistance_le {L : Length} (a b s q : Time) (ω : ConfigurationPath 1 L) :
    torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ intervalDiameter a b ω := by
  exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm (diameterMap a b ω) (s,q))

lemma intervalDiameter_le {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s q, torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ R) :
    intervalDiameter a b ω ≤ R := by
  apply (ContinuousMap.norm_le _ hR).mpr
  intro p
  change |torusDistance L _ _| ≤ R
  rw [abs_of_nonneg (by unfold torusDistance; positivity)]
  exact h p.1 p.2

lemma intervalTime_reverse (a b s : Time) :
    reverseTime (intervalTime a b s)=intervalTime (reverseTime b) (reverseTime a) (reverseTime s) := by
  apply Subtype.ext
  change 1-((1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ)) = (1-(1-(s:ℝ)))*(1-(b:ℝ))+(1-(s:ℝ))*(1-(a:ℝ))
  ring

lemma intervalDiameter_reverse {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter a b (reverseConfigurationPath 1 L ω)=
      intervalDiameter (reverseTime b) (reverseTime a) ω := by
  apply le_antisymm
  · apply intervalDiameter_le _ _ _ (intervalDiameter_nonneg _ _ _)
    intro s q
    change torusDistance L (ω (reverseTime (intervalTime a b s)) 0)
      (ω (reverseTime (intervalTime a b q)) 0) ≤ _
    simp only [intervalTime_reverse]
    exact intervalDistance_le _ _ _ _ _
  · have hh : reverseTime (reverseTime a)=a := reverseTime_reverse _
    have hh' : reverseTime (reverseTime b)=b := reverseTime_reverse _
    apply intervalDiameter_le _ _ _ (intervalDiameter_nonneg _ _ _)
    intro s q
    have h := intervalDistance_le a b (reverseTime s) (reverseTime q) (reverseConfigurationPath 1 L ω)
    change torusDistance L (ω (reverseTime (intervalTime a b (reverseTime s))) 0)
      (ω (reverseTime (intervalTime a b (reverseTime q))) 0) ≤ _ at h
    simpa only [intervalTime_reverse,reverseTime_reverse] using h

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma mesh_firstTime {m : ℕ} (hm : 0 < m) (s : Time) :
    meshTime (0:Fin (m+1)) s=prefixTime (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) s := by
  apply Subtype.ext
  simp only [meshTime,Fin.val_zero,Nat.cast_zero,zero_add,prefixTime,ContinuousMap.coe_mk,splitTime,Nat.cast_add,Nat.cast_one]
  ring

lemma mesh_nextTime {m : ℕ} (hm : 0 < m) (j : Fin m) (s : Time) :
    meshTime j.succ s=suffixTime (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) (meshTime j s) := by
  apply Subtype.ext
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hm1 : (1:ℝ)+m≠0 := by positivity
  simp only [meshTime,Fin.val_succ,suffixTime,ContinuousMap.coe_mk,splitTime,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

lemma meshSegment_first {m : ℕ} {L : Length} (hm : 0 < m) (ω : ConfigurationPath 1 L) :
    meshSegment (0:Fin (m+1)) ω=configurationPrefix 1 L (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) ω := by
  ext s i j
  exact congrArg (fun u : Time ↦ ω u i j) (mesh_firstTime hm s)

lemma meshSegment_next {m : ℕ} {L : Length} (hm : 0 < m) (j : Fin m) (ω : ConfigurationPath 1 L) :
    meshSegment j.succ ω=meshSegment j (configurationSuffix 1 L (splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm)) ω) := by
  ext s i k
  exact congrArg (fun u : Time ↦ ω u i k) (mesh_nextTime hm j s)

lemma meshTime_reverse {m : ℕ} (j : Fin m) (s : Time) :
    reverseTime (meshTime j s)=meshTime j.rev (reverseTime s) := by
  apply Subtype.ext
  have hm : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  change 1-((j:ℝ)+(s:ℝ))/(m:ℝ)=((j.rev:ℝ)+(1-(s:ℝ)))/(m:ℝ)
  have hj : (j.rev:ℝ)=(m:ℝ)-1-(j:ℝ) := by
    rw [Fin.val_rev,Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hj]
  field_simp
  ring

lemma meshSegment_reverse {m : ℕ} {L : Length} (j : Fin m) (ω : ConfigurationPath 1 L) :
    meshSegment j (reverseConfigurationPath 1 L ω)=reverseConfigurationPath 1 L (meshSegment j.rev ω) := by
  ext s i k
  exact congrArg (fun u : Time ↦ ω u i k) (meshTime_reverse j s)

lemma mesh_sum_reverse {m : ℕ} {L : Length} (F : ConfigurationPath 1 L→ℝ)
    (hF : ∀ω,F (reverseConfigurationPath 1 L ω)=F ω) (ω : ConfigurationPath 1 L) :
    ∑ j : Fin m,F (meshSegment j (reverseConfigurationPath 1 L ω))=
    ∑ j : Fin m,F (meshSegment j ω) := by
  simp only [meshSegment_reverse,hF]
  exact Equiv.sum_comp (Fin.revPerm) (fun j : Fin m ↦ F (meshSegment j ω))

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledObservable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

lemma split_fixedTrajectory_measurable (N : ℕ) (L : Length) (s t : ℝ)
    (X : Configuration N L) :
    Measurable (fun p : CoordinatePaths N × CoordinatePaths N ↦
      (freeTrajectory N L s p.1 X,
        freeTrajectory N L t p.2 (freeTrajectory N L s p.1 X 1))) := by
  exact ((freeTrajectory_continuous N L s |>.comp (continuous_fst.prodMk continuous_const)).prodMk
    (freeTrajectory_continuous N L t |>.comp (continuous_snd.prodMk
      ((freeTrajectory_continuous N L s |>.comp (continuous_fst.prodMk continuous_const)).eval continuous_const)))).measurable

lemma split_fixedTrajectory (N : ℕ) (L : Length) (s t : ℝ) (hs : 0 < s) (ht : 0<t)
    (w : CoordinatePaths N) (X : Configuration N L) :
    (configurationPrefix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X),
      configurationSuffix N L (splitTime s t hs ht) (freeTrajectory N L (s+t) w X)) =
      (freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X,
        freeTrajectory N L t (fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p))
          (freeTrajectory N L s (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p)) X 1)) := by
  apply Prod.ext
  · exact prefix_freeTrajectory N L s t hs ht w X
  · dsimp only [Prod.snd]
    rw [suffix_freeTrajectory N L s t hs ht]
    congr 1
    have heq := congrArg (fun ω : ConfigurationPath N L ↦ ω 1)
      (prefix_freeTrajectory N L s t hs ht w X)
    simpa only [configurationPrefix,ContinuousMap.comp_apply,prefixTime_one] using heq

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma meshProduct_measurable {L : Length} (m : ℕ) {F : ConfigurationPath 1 L → ℝ≥0∞}
    (hF : Measurable F) : Measurable (meshProduct m F) := by
  unfold meshProduct
  exact Finset.measurable_prod _ (fun j _ ↦ hF.comp (meshSegment_continuous L j).measurable)

lemma splitTime_mul {τ : ℝ} (hτ : 0<τ) {m : ℕ} (hm : 0 < m) :
    splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)=
      splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm) := by
  apply Subtype.ext
  change τ/(τ+(m:ℝ)*τ)=1/(1+(m:ℝ))
  have hτ' := ne_of_gt hτ
  have hm' : (1:ℝ)+(m:ℝ)≠0 := by positivity
  field_simp

lemma meshProduct_succ {L : Length} {m : ℕ} (hm : 0 < m) (F : ConfigurationPath 1 L → ℝ≥0∞)
    {τ : ℝ} (hτ : 0<τ) (ω : ConfigurationPath 1 L) :
    meshProduct (m+1) F ω =
      F (configurationPrefix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω)*
      meshProduct m F (configurationSuffix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω) := by
  rw [splitTime_mul hτ hm]
  simp only [meshProduct,Fin.prod_univ_succ,meshSegment_first hm,meshSegment_next hm]

lemma meshProduct_free_bound {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    {τ : ℝ} (hτ : 0<τ) (B : ℝ≥0∞)
    (hB : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L τ w X) ∂coordinateWiener 1 ≤ B) :
    ∀ m : ℕ, 0 < m → ∀ X : Configuration 1 L,
      ∫⁻w, meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 ≤ B^m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hB
  | succ m hm ih =>
    intro X
    let u := splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)
    let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
      F (freeTrajectory 1 L τ w.1 X) *
      meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))
    have hfirst : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w.1 X)) :=
      hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_fst.prodMk continuous_const)).measurable
    have hsecond : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦
        meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))) :=
      (meshProduct_measurable m hF).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable 1 L τ ((m:ℝ)*τ) X))
    have hG : Measurable G := hfirst.mul hsecond
    have he (w : CoordinatePaths 1) :
        meshProduct (m+1) F (freeTrajectory 1 L (((m+1:ℕ):ℝ)*τ) w X)=
        G (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)) := by
      have hmul : (((m+1:ℕ):ℝ)*τ)=τ+(m:ℝ)*τ := by push_cast; ring
      rw [hmul,meshProduct_succ hm F hτ]
      have hp := congrArg Prod.fst (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      have hq := congrArg Prod.snd (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      dsimp only [Prod.fst,Prod.snd] at hp hq
      rw [hp,hq]
    calc
      _ = ∫⁻w,G (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p)) ∂coordinateWiener 1 := lintegral_congr he
      _ = ∫⁻w,G w ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
        (coordinateSplit_preserving 1 u (splitTime_pos _ _ _ _) (splitTime_lt_one _ _ _ _)).lintegral_comp hG
      _ = ∫⁻w₁,∫⁻w₂,G (w₁,w₂) ∂coordinateWiener 1 ∂coordinateWiener 1 := lintegral_prod _ hG.aemeasurable
      _ ≤ ∫⁻w₁,F (freeTrajectory 1 L τ w₁ X)*B^m ∂coordinateWiener 1 := by
        apply lintegral_mono
        intro w₁
        dsimp only [G]
        have hmeas : Measurable (fun w₂ : CoordinatePaths 1 ↦
            meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w₂ (freeTrajectory 1 L τ w₁ X 1))) :=
          (meshProduct_measurable m hF).comp
            ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_const_mul _ hmeas]
        exact mul_le_mul_right (ih _) _
      _ = (∫⁻w₁,F (freeTrajectory 1 L τ w₁ X) ∂coordinateWiener 1)*B^m :=
        lintegral_mul_const _ (hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable)
      _ ≤ B*B^m := mul_le_mul_left (hB X) _
      _ = B^(m+1) := by rw [pow_succ]; exact mul_comm _ _

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma meshSum_measurable {L : Length} (m : ℕ) {F : ConfigurationPath 1 L → ℝ≥0∞}
    (hF : Measurable F) : Measurable (meshSum m F) := by
  unfold meshSum
  exact Finset.measurable_sum _ (fun j _ ↦ hF.comp (meshSegment_continuous L j).measurable)

lemma meshSum_succ {L : Length} {m : ℕ} (hm : 0 < m) (F : ConfigurationPath 1 L → ℝ≥0∞)
    {τ : ℝ} (hτ : 0<τ) (ω : ConfigurationPath 1 L) :
    meshSum (m+1) F ω =
      F (configurationPrefix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω)+
      meshSum m F (configurationSuffix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω) := by
  rw [splitTime_mul hτ hm]
  simp only [meshSum,Fin.sum_univ_succ,meshSegment_first hm,meshSegment_next hm]

lemma meshSum_free_bound {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    {τ : ℝ} (hτ : 0<τ) (B : ℝ≥0∞)
    (hB : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L τ w X) ∂coordinateWiener 1 ≤ B) :
    ∀ m : ℕ, 0 < m → ∀ X : Configuration 1 L,
      ∫⁻w, meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 ≤ (m:ℝ≥0∞)*B := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hB
  | succ m hm ih =>
    intro X
    let u := splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)
    let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
      F (freeTrajectory 1 L τ w.1 X) +
      meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))
    have hfirst : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w.1 X)) :=
      hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_fst.prodMk continuous_const)).measurable
    have hsecond : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦
        meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))) :=
      (meshSum_measurable m hF).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable 1 L τ ((m:ℝ)*τ) X))
    have hG : Measurable G := hfirst.add hsecond
    have he (w : CoordinatePaths 1) :
        meshSum (m+1) F (freeTrajectory 1 L (((m+1:ℕ):ℝ)*τ) w X)=
        G (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)) := by
      have hmul : (((m+1:ℕ):ℝ)*τ)=τ+(m:ℝ)*τ := by push_cast; ring
      rw [hmul,meshSum_succ hm F hτ]
      have hp := congrArg Prod.fst (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      have hq := congrArg Prod.snd (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      dsimp only [Prod.fst,Prod.snd] at hp hq
      rw [hp,hq]
    calc
      _ = ∫⁻w,G (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p)) ∂coordinateWiener 1 := lintegral_congr he
      _ = ∫⁻w,G w ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
        (coordinateSplit_preserving 1 u (splitTime_pos _ _ _ _) (splitTime_lt_one _ _ _ _)).lintegral_comp hG
      _ = ∫⁻w₁,∫⁻w₂,G (w₁,w₂) ∂coordinateWiener 1 ∂coordinateWiener 1 := lintegral_prod _ hG.aemeasurable
      _ ≤ ∫⁻w₁,F (freeTrajectory 1 L τ w₁ X)+(m:ℝ≥0∞)*B ∂coordinateWiener 1 := by
        apply lintegral_mono
        intro w₁
        dsimp only [G]
        have hmeas : Measurable (fun w₂ : CoordinatePaths 1 ↦
            meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w₂ (freeTrajectory 1 L τ w₁ X 1))) :=
          (meshSum_measurable m hF).comp
            ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
        exact add_le_add le_rfl (ih _)
      _ = (∫⁻w₁,F (freeTrajectory 1 L τ w₁ X) ∂coordinateWiener 1)+(m:ℝ≥0∞)*B := by
        have hmeas : Measurable (fun w : CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w X)) := hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_add_left hmeas,lintegral_const,measure_univ,mul_one]
      _ ≤ B+(m:ℝ≥0∞)*B := add_le_add (hB X) le_rfl
      _ = ((m+1:ℕ):ℝ≥0∞)*B := by push_cast; ring

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_WienerGaussian
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma norm_tent_combination_le (n : ℕ) (c : Fin (2^n) → ℝ)
    (hc : ∀ k, |c k| ≤ 1) : ‖∑ k, c k • tentMap n k‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  calc
    |∑ k, c k * tentMap n k t| ≤ ∑ k, |c k * tentMap n k t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, tent n k t := by
      apply Finset.sum_le_sum
      intro k _
      change |c k * tent n k t|≤_
      rw [abs_mul, abs_of_nonneg (tent_nonneg n k t)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc k) (tent_nonneg n k t)
    _ ≤ 1 := sum_tent_le_one n t

lemma dual_tent_sum_abs_le (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) :
    ∑ k, |L (tentMap n k)| ≤ ‖L‖ := by
  classical
  let c : Fin (2^n) → ℝ := fun k ↦ if 0 ≤ L (tentMap n k) then 1 else -1
  have hc : ∀ k, |c k|≤1 := by intro k; simp only [c]; split <;> norm_num
  have he : L (∑ k, c k • tentMap n k) = ∑ k, |L (tentMap n k)| := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul]
    simp only [smul_eq_mul,c]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  calc
    ∑ k, |L (tentMap n k)| ≤ |L (∑ k, c k • tentMap n k)| := by rw [he]; exact le_abs_self _
    _ ≤ ‖L‖ * ‖∑ k, c k • tentMap n k‖ := L.le_opNorm _
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left (norm_tent_combination_le n c hc) (L.opNorm_nonneg)
    _ = ‖L‖ := mul_one _

lemma dual_tent_sum_sq_le (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) :
    ∑ k, L (tentMap n k)^2 ≤ ‖L‖^2 := by
  have h := dual_tent_sum_abs_le L n
  calc
    ∑ k, L (tentMap n k)^2 = ∑ k, |L (tentMap n k)|^2 := by simp
    _ ≤ (∑ k, |L (tentMap n k)|)^2 := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [sq]
      exact Finset.single_le_sum (f := fun j ↦ |L (tentMap n k)| * |L (tentMap n j)|)
        (fun j _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ k)
    _ ≤ ‖L‖^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) h 2

lemma amplitude_sq (n : ℕ) : amplitude n ^ 2 = (1/4:ℝ)*(1/2:ℝ)^n := by
  simp only [amplitude,mul_pow]
  rw [←pow_mul,Nat.mul_comm n 2,pow_mul,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num

lemma dual_variance_summable (L : C(Time,ℝ) →L[ℝ] ℝ) :
    Summable (fun n ↦ amplitude n^2 * ∑ k, L (tentMap n k)^2) := by
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity)
    (fun n ↦ mul_le_mul_of_nonneg_left (dual_tent_sum_sq_le L n) (sq_nonneg _))
  simp_rw [amplitude_sq]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left ((1/4:ℝ)*‖L‖^2)

lemma dual_partialPath_expansion (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) (ω : Noise) :
    L (partialPath n ω) = ∑ i, dualCoefficient L n i * ω (partialEmbed n i) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,dualCoefficient,partialEmbed,
    Fintype.sum_unique,partialPath,map_add,map_smul,map_sum,level,smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m), amplitude m * L (tentMap m k) * ω (.inr ⟨m,k⟩)) n]
  congr 1
  · change ω (.inl ()) * L linearPath = L linearPath * ω (.inl ())
    ring
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma dual_partial_variance (L : C(Time,ℝ) →L[ℝ] ℝ) (n : ℕ) :
    (∑ i : PartialIndex n, dualCoefficient L n i ^ 2) =
      L linearPath ^ 2 + ∑ m ∈ Finset.range n, amplitude m^2 * ∑ k, L (tentMap m k)^2 := by
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,dualCoefficient,Fintype.sum_unique,mul_pow,←Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ amplitude m^2 * ∑ k, L (tentMap m k)^2) n]

lemma dual_path_law (L : C(Time,ℝ) →L[ℝ] ℝ) :
    HasLaw (fun ω ↦ L (path ω))
      (gaussianReal 0 (Real.toNNReal (L linearPath^2 + ∑' n, amplitude n^2 * ∑ k, L (tentMap n k)^2))) law := by
  have hv : Tendsto (fun n ↦ Real.toNNReal (∑ i : PartialIndex n, dualCoefficient L n i ^2)) atTop
      (𝓝 (Real.toNNReal (L linearPath^2 + ∑' n, amplitude n^2 * ∑ k, L (tentMap n k)^2))) := by
    simp_rw [dual_partial_variance]
    exact continuous_real_toNNReal.tendsto _ |>.comp
      (tendsto_const_nhds.add ((dual_variance_summable L).hasSum.tendsto_sum_nat))
  apply hasLaw_gaussian_of_ae_tendsto (X := fun n ω ↦ L (partialPath n ω)) (m := fun _ ↦ 0)
    (v := fun n ↦ Real.toNNReal (∑ i : PartialIndex n, dualCoefficient L n i^2)) _ _ tendsto_const_nhds hv
  · intro n
    have h := finite_coordinate_law n (dualCoefficient L n)
    simp_rw [←dual_partialPath_expansion] at h
    convert h using 2
    all_goals try with_reducible_and_instances rfl
    rw [Real.toNNReal_sum_of_nonneg (fun i _ ↦ sq_nonneg (dualCoefficient L n i))]
    apply Finset.sum_congr rfl
    intro i _
    exact Real.toNNReal_of_nonneg (sq_nonneg _)
  · filter_upwards [ae_partialPath_tendsto] with ω hω
    exact L.continuous.tendsto _ |>.comp hω

instance wiener_isGaussian : IsGaussian wiener := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  refine ⟨0,Real.toNNReal (L linearPath^2 + ∑' n, amplitude n^2 * ∑ k, L (tentMap n k)^2),?_⟩
  rw [wiener,Measure.map_map L.continuous.measurable measurable_path]
  exact (dual_path_law L).map_eq

theorem wiener_exists_integrable_exp_sq :
    ∃ c, 0 < c ∧ Integrable (fun w : C(Time,ℝ) ↦ Real.exp (c*‖w‖^2)) wiener :=
  IsGaussian.exists_integrable_exp_sq wiener

theorem wiener_norm_gaussian_tail :
    ∃ (c : ℝ) (M : ℝ≥0∞), 0 < c ∧ M<⊤ ∧ ∀ R : ℝ, 0≤R →
      wiener {w | R≤‖w‖} ≤ M * ENNReal.ofReal (Real.exp (-c*R^2)) := by
  obtain ⟨c,hc,hi⟩ := wiener_exists_integrable_exp_sq
  let M := ∫⁻ w : C(Time,ℝ), ENNReal.ofReal (Real.exp (c*‖w‖^2)) ∂wiener
  have hM : M<⊤ := by
    dsimp [M]
    rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))]
    exact ENNReal.ofReal_lt_top
  refine ⟨c,M,hc,hM,?_⟩
  intro R hR
  have hsub : {w : C(Time,ℝ) | R≤‖w‖} ⊆
      {w | ENNReal.ofReal (Real.exp (c*R^2))≤ENNReal.ofReal (Real.exp (c*‖w‖^2))} := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hw 2) hc.le)
  apply (measure_mono hsub).trans
  have hm : Measurable (fun w : C(Time,ℝ) ↦ ENNReal.ofReal (Real.exp (c*‖w‖^2))) := by fun_prop
  have hh := meas_ge_le_lintegral_div (μ := wiener) hm.aemeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (c*R^2)))) ENNReal.ofReal_ne_top
  apply hh.trans_eq
  change M / ENNReal.ofReal (Real.exp (c*R^2)) = M * ENNReal.ofReal (Real.exp (-c*R^2))
  rw [div_eq_mul_inv,←ENNReal.ofReal_inv_of_pos (Real.exp_pos _),←Real.exp_neg]
  congr 3
  ring

end HardSphere.Wiener

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitPacking
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Wiener.wiener_isGaussian _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HardSphere
open MeasureTheory Wiener Set
attribute [local irreducible] torusDistance

lemma pathVisitsBall_isClosed {n : ℕ} (L : Length) (R : ℝ) (v : Torus L) (i : Fin n) :
    IsClosed {ω : ConfigurationPath n L | pathVisitsBall L R v i ω} := by
  have hc : Continuous (fun p : ConfigurationPath n L × Time ↦ torusDistance L (p.1 p.2 i) v) := by
    have he : Continuous (fun p : ConfigurationPath n L × Time ↦ p.1 p.2 i) :=
      (continuous_apply i).comp (continuous_eval : Continuous (fun p : ConfigurationPath n L × Time ↦ p.1 p.2))
    exact (continuous_torusDistance L).comp (he.prodMk continuous_const)
  have hs := isClosedMap_fst_of_compactSpace
    {p : ConfigurationPath n L × Time | torusDistance L (p.1 p.2 i) v ≤ R}
    (isClosed_le hc continuous_const)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  simp only [pathVisitsBall,Set.mem_ofPred_eq,Set.mem_image,Prod.exists]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨ω,q,hq,rfl⟩
  · rintro ⟨ω',q,hq,rfl⟩
    exact ⟨q,hq⟩

end HardSphere

namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

lemma freeTrajectory_coord_dist_le {n : ℕ} (L : Length) (t : ℝ) (w : CoordinatePaths n)
    (X : Configuration n L) (i : Fin n) (u : Time) (j : Fin 3) :
    dist (freeTrajectory n L t w X u i j) (X i j) ≤ Real.sqrt (2*t)*‖w (i,j)‖ := by
  change dist (X i j+((Real.sqrt (2*t)*w (i,j) u:ℝ):AddCircle L.val)) (X i j) ≤ _
  simp only [dist_eq_norm,add_sub_cancel_left]
  calc
    ‖((Real.sqrt (2*t)*w (i,j) u:ℝ):AddCircle L.val)‖ ≤ ‖Real.sqrt (2*t)*w (i,j) u‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = Real.sqrt (2*t)*|w (i,j) u| := by rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (w (i,j)) u) (Real.sqrt_nonneg _)

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FreeVisitTravel
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice

lemma torusDistance_le_three_of_coord (L : Length) (x y : Torus L) {B : ℝ}
    (hB : 0≤B) (h : ∀ j, dist (x j) (y j)≤B) : torusDistance L x y≤3*B := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hs : ∑ j : Fin 3, dist (x j) (y j)^2 ≤ ∑ _j : Fin 3, B^2 :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ dist_nonneg (h j) 2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    norm_num at hs
    nlinarith [sq_nonneg B]

attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

end HardSphere.FreeVisits

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_MeshEvents
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma meshEvent_measurable {L : Length} (m : ℕ) {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) :
    MeasurableSet (meshEvent m E) := by
  simp only [meshEvent,ofPred_exists]
  exact MeasurableSet.iUnion (fun j ↦ hE.preimage (meshSegment_continuous L j).measurable)

lemma meshEvent_free_bound {L : Length} (m : ℕ) (hm : 0 < m) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) {τ : ℝ} (hτ : 0<τ) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, coordinateWiener 1 {w | freeTrajectory 1 L τ w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} ≤ (m:ℝ≥0∞)*p := by
  let F : ConfigurationPath 1 L → ℝ≥0∞ := E.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hB (Y : Configuration 1 L) : ∫⁻ w,F (freeTrajectory 1 L τ w Y) ∂coordinateWiener 1 ≤ p := by
    have hEv : MeasurableSet {w | freeTrajectory 1 L τ w Y ∈ E} :=
      hE.preimage ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻ w,({w | freeTrajectory 1 L τ w Y ∈ E}.indicator (fun _ ↦ 1)) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const hEv,one_mul] using hp Y
  have hEv : MeasurableSet {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} :=
    (meshEvent_measurable m hE).preimage ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
  calc
    _ = ∫⁻w,({w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 :=
      by rw [lintegral_indicator_const hEv,one_mul]
    _ ≤ ∫⁻w,meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 := by
      apply lintegral_mono
      intro w
      by_cases hw : freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E
      · rw [Set.indicator_of_mem (show w ∈ {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} from hw)]
        obtain ⟨j,hj⟩ := hw
        have hle := Finset.single_le_sum (f := fun j : Fin m ↦ F (meshSegment j (freeTrajectory 1 L ((m:ℝ)*τ) w X)))
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)
        simpa only [F,meshSum,Set.indicator_of_mem hj] using hle
      · rw [Set.indicator_of_notMem (show w ∉ {w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m E} from hw)]
        exact bot_le
    _ ≤ (m:ℝ≥0∞)*p := meshSum_free_bound F hF hτ p hB m hm X

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.PathCutoff

lemma exp_cap_le {x B : ℝ} (hB : 0 < B) (hx : 0 ≤ x) :
    Real.exp (min x B/B)  ≤  1+(Real.exp 1-1)*x/B := by
  have h0 : 0 ≤ min x B/B := div_nonneg (le_min hx hB.le) hB.le
  have h1 : min x B/B ≤ 1 := (div_le_one hB).mpr (min_le_right _ _)
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    (sub_nonneg.mpr h1) h0 (by ring : 1-min x B/B+min x B/B=1)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at h
  calc
    Real.exp (min x B/B) ≤ 1+(Real.exp 1-1)*(min x B)/B := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _  ≤  1+(Real.exp 1-1)*x/B := by
      gcongr
      · exact sub_nonneg.mpr (by simp)
      · exact min_le_left _ _

lemma exp_cap_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω→ℝ} (hX : Integrable X μ) (hX0 : ∀ᵐω ∂μ,0 ≤ X ω) {B : ℝ} (hB : 0 < B) :
    ∫⁻ω, ENNReal.ofReal (Real.exp (min (X ω) B/B)) ∂μ  ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1-1)*(∫ω,X ω ∂μ)/B)) := by
  have hi : Integrable (fun ω ↦ 1+(Real.exp 1-1)*X ω/B) μ :=
    (integrable_const 1).add ((hX.const_mul _).div_const _)
  calc
    _  ≤  ∫⁻ω,ENNReal.ofReal (1+(Real.exp 1-1)*X ω/B) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hX0] with ω hω
      exact ENNReal.ofReal_le_ofReal (exp_cap_le hB hω)
    _ = ENNReal.ofReal (1+(Real.exp 1-1)*(∫ω,X ω ∂μ)/B) := by
      rw [←ofReal_integral_eq_lintegral_ofReal hi]
      · congr 1
        rw [integral_add (integrable_const _) ((hX.const_mul _).div_const _),integral_const,
          integral_div,integral_const_mul,probReal_univ,one_smul]
      · filter_upwards [hX0] with ω hω
        have he : 0 ≤ Real.exp 1-1 := sub_nonneg.mpr (by simp)
        positivity
    _  ≤  _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp ((Real.exp 1-1)*(∫ω,X ω ∂μ)/B)])

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits BathSlice
attribute [local irreducible] torusDistance freeTrajectory

lemma noiseSize_nonneg (w : CoordinatePaths 1) : 0 ≤ noiseSize w :=
  Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
lemma noiseSize_coord (w : CoordinatePaths 1) (j : Fin 3) : ‖w (0,j)‖ ≤ noiseSize w :=
  by
    change ‖w (0,j)‖ ≤ ∑ i : Fin 3, ‖w (0,i)‖
    exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (w (0,i))) (Finset.mem_univ j)

lemma free_diameter_le (L : Length) (t : ℝ) (w : CoordinatePaths 1) (y : Torus L) {R : ℝ}
    (hR : 0 ≤ R) (hw : ∀ j, ‖w (0,j)‖ ≤ R) :
    intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y)) ≤ 6*Real.sqrt (2*t)*R := by
  have hd (s : Time) : torusDistance L (freeTrajectory 1 L t w (oneConfiguration y) s 0) y ≤
      3*(Real.sqrt (2*t)*R) := by
    apply torusDistance_le_three_of_coord L _ _ (by positivity)
    intro j
    apply (freeTrajectory_coord_dist_le L t w (oneConfiguration y) 0 s j).trans
    exact mul_le_mul_of_nonneg_left (hw j) (Real.sqrt_nonneg _)
  apply intervalDiameter_le _ _ _ (by positivity)
  intro s q
  have htri := torusDistance_triangle' L
    (freeTrajectory 1 L t w (oneConfiguration y) (intervalTime 0 1 s) 0) y
    (freeTrajectory 1 L t w (oneConfiguration y) (intervalTime 0 1 q) 0)
  rw [torusDistance_comm L y] at htri
  linarith [hd (intervalTime 0 1 s), hd (intervalTime 0 1 q)]

lemma free_diameter_noise (L : Length) {t r : ℝ} (hr : 0 < r) (ht : t ≤ r^2)
    (w : CoordinatePaths 1) (y : Torus L) :
    intervalDiameter 0 1 (freeTrajectory 1 L t w (oneConfiguration y))/r ≤ 12*noiseSize w := by
  have hs : Real.sqrt (2*t) ≤ 2*r := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith [sq_nonneg r]⟩
  have h := free_diameter_le L t w y (noiseSize_nonneg w) (noiseSize_coord w)
  apply (div_le_iff₀ hr).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 6*noiseSize w from mul_nonneg (by norm_num) (noiseSize_nonneg w))
  nlinarith

lemma noiseSize_memLp (p : ℝ≥0∞) (hp : p≠⊤) : MemLp noiseSize p (coordinateWiener 1) := by
  unfold noiseSize
  apply memLp_finsetSum
  intro j _
  exact ((IsGaussian.memLp_id wiener p hp).norm).comp_measurePreserving
    (measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,j))

lemma integrable_cubicNoise : Integrable (fun w : CoordinatePaths 1 ↦ (1+12*noiseSize w)^3) (coordinateWiener 1) := by
  have h0 : MemLp (fun _ : CoordinatePaths 1 ↦ (1:ℝ)) (3:ℝ≥0∞) (coordinateWiener 1) := memLp_const 1
  have h1 := (noiseSize_memLp 3 (by norm_num)).const_mul 12
  have h : MemLp (fun w : CoordinatePaths 1 ↦ 1+12*noiseSize w) (3:ℝ≥0∞) (coordinateWiener 1) := h0.add h1
  have hi := h.integrable_norm_pow (by norm_num : (3:ℕ)≠0)
  have hpos (w : CoordinatePaths 1) : 0 ≤ 1+12*noiseSize w := by have := noiseSize_nonneg w; positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hi

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CubicMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma diameterRatio_nonneg {L : Length} {r : ℝ} (hr : 0 ≤ r) (ω : ConfigurationPath 1 L) : 0≤diameterRatio r ω :=
  div_nonneg (intervalDiameter_nonneg 0 1 ω) hr
lemma cubicCost_nonneg {L : Length} {r : ℝ} (hr : 0 ≤ r) (ω : ConfigurationPath 1 L) : 0 ≤ cubicCost r ω := by
  unfold cubicCost
  have := diameterRatio_nonneg hr ω
  positivity
lemma cubicCost_reverse {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    cubicCost r (reverseConfigurationPath 1 L ω)=cubicCost r ω := by
  unfold cubicCost diameterRatio
  rw [intervalDiameter_reverse]
  have h1 : reverseTime 1=0 := by apply Subtype.ext; norm_num [reverseTime]
  have h0 : reverseTime 0=1 := by apply Subtype.ext; norm_num [reverseTime]
  rw [h1,h0]

lemma free_cubicCost_le {L : Length} {r t : ℝ} (hr : 0 < r) (ht : t ≤ r^2)
    (w : CoordinatePaths 1) (X : Configuration 1 L) :
    cubicCost r (freeTrajectory 1 L t w X) ≤ (1+12*noiseSize w)^3 := by
  have hX : X=oneConfiguration (X 0) := by ext i j; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
  have h := free_diameter_noise L hr ht w (X 0)
  rw [←hX] at h
  unfold cubicCost diameterRatio
  exact pow_le_pow_left₀ (by have := intervalDiameter_nonneg 0 1 (freeTrajectory 1 L t w X); positivity) (add_le_add le_rfl h) 3

lemma free_cubicCost_integrable {L : Length} {r t : ℝ} (hr : 0 < r) (ht : t ≤ r^2)
    (X : Configuration 1 L) :
    Integrable (fun w ↦ cubicCost r (freeTrajectory 1 L t w X)) (coordinateWiener 1) := by
  apply integrable_cubicNoise.mono'
    (((cubicCost_continuous L r).comp ((freeTrajectory_continuous 1 L t).comp
      (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
  exact ae_of_all _ (fun w ↦ by
    change ‖cubicCost r (freeTrajectory 1 L t w X)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (cubicCost_nonneg hr.le _)]
    exact free_cubicCost_le hr ht w X)

lemma cubicMean_nonneg : 0 ≤ cubicMean := integral_nonneg (fun w ↦ by have := noiseSize_nonneg w; positivity)

lemma free_cubicMean_le {L : Length} {r t : ℝ} (hr : 0 < r) (ht : t ≤ r^2) (X : Configuration 1 L) :
    ∫w,cubicCost r (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤ cubicMean :=
  integral_mono (free_cubicCost_integrable hr ht X) integrable_cubicNoise (fun w ↦ free_cubicCost_le hr ht w X)

lemma cappedWeight_measurable {L : Length} (r B : ℝ) : Measurable (cappedWeight (L:=L) r B) :=
  (Real.continuous_exp.comp (((cubicCost_continuous L r).min continuous_const).div_const B)).measurable.ennreal_ofReal

lemma meanCost_nonneg : 0 ≤ meanCost := by
  unfold meanCost
  have he : 0≤Real.exp 1-1 := by have := Real.add_one_le_exp 1; linarith
  exact mul_nonneg he cubicMean_nonneg

lemma free_cap_moment {L : Length} {r t B : ℝ} (hr : 0 < r) (ht : t ≤ r^2) (hB : 0<B)
    (X : Configuration 1 L) :
    ∫⁻w,cappedWeight r B (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤
      ENNReal.ofReal (Real.exp (meanCost/B)) := by
  apply (exp_cap_integral (coordinateWiener 1) (free_cubicCost_integrable hr ht X)
    (ae_of_all _ (fun _ ↦ cubicCost_nonneg hr.le _)) hB).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold meanCost
  apply div_le_div_of_nonneg_right _ hB.le
  apply mul_le_mul_of_nonneg_left (free_cubicMean_le hr ht X)
  have := Real.add_one_le_exp 1
  linarith

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma capSum_continuous {L : Length} (m : ℕ) (r B : ℝ) : Continuous (capSum (L:=L) m r B) := by
  unfold capSum
  exact continuous_finsetSum _ (fun j _ ↦ ((cubicCost_continuous L r).comp (meshSegment_continuous L j)).min continuous_const)

lemma cap_product_eq {L : Length} (m : ℕ) (r B : ℝ) (ω : ConfigurationPath 1 L) :
    meshProduct m (cappedWeight r B) ω=ENNReal.ofReal (Real.exp (capSum m r B ω/B)) := by
  simp only [meshProduct,cappedWeight,capSum,Finset.sum_div,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _)]

lemma orig_exp_pow (x : ℝ) (m : ℕ) :
    (ENNReal.ofReal (Real.exp x))^m=ENNReal.ofReal (Real.exp ((m:ℝ)*x)) := by
  rw [←ENNReal.ofReal_pow (Real.exp_nonneg x),←Real.exp_nat_mul]

lemma mesh_cap_moment {L : Length} {r τ B : ℝ} (hr : 0 < r) (hτ : 0<τ) (hτr : τ ≤ r^2) (hB : 0<B)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    ∫⁻w,ENNReal.ofReal (Real.exp (capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)/B)) ∂coordinateWiener 1 ≤
      ENNReal.ofReal (Real.exp ((m:ℝ)*meanCost/B)) := by
  have h := meshProduct_free_bound (cappedWeight r B) (cappedWeight_measurable r B) hτ
    (ENNReal.ofReal (Real.exp (meanCost/B))) (fun Y ↦ free_cap_moment hr hτr hB Y) m hm X
  simpa only [cap_product_eq,orig_exp_pow,mul_div_assoc] using h

lemma mesh_cap_tail {L : Length} {r τ B : ℝ} (hr : 0 < r) (hτ : 0<τ) (hτr : τ ≤ r^2) (hB : 0<B)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    coordinateWiener 1 {w | (meanCost+1)*(m:ℝ) ≤ capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      ENNReal.ofReal (Real.exp (-(m:ℝ)/B)) := by
  let F : CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
    ENNReal.ofReal (Real.exp (capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)/B))
  let v : ℝ≥0∞ := ENNReal.ofReal (Real.exp (((meanCost+1)*(m:ℝ))/B))
  have hF : Measurable F :=
    (Real.continuous_exp.comp (((capSum_continuous m r B).comp ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp
      (continuous_id.prodMk continuous_const))).div_const B)).measurable.ennreal_ofReal
  have hv : v≠0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hv' : v≠⊤ := ENNReal.ofReal_ne_top
  have hsub : {w | (meanCost+1)*(m:ℝ) ≤ capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ⊆ {w | v ≤ F w} := by
    intro w hw
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hw hB.le))
  calc
    _ ≤ coordinateWiener 1 {w | v ≤ F w} := measure_mono hsub
    _ ≤ (∫⁻w,F w ∂coordinateWiener 1)/v := meas_ge_le_lintegral_div hF.aemeasurable hv hv'
    _ ≤ ENNReal.ofReal (Real.exp ((m:ℝ)*meanCost/B))/v :=
      ENNReal.div_le_div_right (mesh_cap_moment hr hτ hτr hB m hm X) v
    _ = ENNReal.ofReal (Real.exp (-(m:ℝ)/B)) := by
      dsimp only [v]
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_DiameterTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma free_diameterRatio_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R : ℝ} (hr : 0 < r) (hτr : τ ≤ r^2) (hR : 0≤R)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | R<diameterRatio r (freeTrajectory 1 L τ w X)} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)) := by
  have hX : X=oneConfiguration (X 0) := by ext i j; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
  have hsub : {w | R<diameterRatio r (freeTrajectory 1 L τ w X)} ⊆
      ⋃j : Fin 3,{w | R/36≤‖w (0,j)‖} := by
    intro w hw
    by_contra hn
    have hnorm : ∀j : Fin 3, ‖w (0,j)‖<R/36 := by
      simpa only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_le] using hn
    have hsum : noiseSize w ≤ R/12 := by
      unfold noiseSize
      calc
        _ ≤ ∑j : Fin 3, R/36 := Finset.sum_le_sum (fun j _ ↦ (hnorm j).le)
        _ = R/12 := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]; ring
    have hd := free_diameter_noise L hr hτr w (X 0)
    rw [←hX] at hd
    change R < intervalDiameter 0 1 (freeTrajectory 1 L τ w X)/r at hw
    linarith
  have he (j : Fin 3) : coordinateWiener 1 {w | R/36≤‖w (0,j)‖} = wiener {w | R/36≤‖w‖} :=
    (measurePreserving_eval (fun _ : Direction 1 ↦ wiener) (0,j)).measure_preimage
      (measurableSet_le measurable_const measurable_norm).nullMeasurableSet
  calc
    _ ≤ coordinateWiener 1 (⋃j : Fin 3,{w | R/36≤‖w (0,j)‖}) := measure_mono hsub
    _ ≤ ∑'j : Fin 3,coordinateWiener 1 {w | R/36≤‖w (0,j)‖} := measure_iUnion_le _
    _ = 3*wiener {w | R/36≤‖w‖} := by simp [he,tsum_fintype]
    _ ≤ 3*(M*ENNReal.ofReal (Real.exp (-c*(R/36)^2))) := mul_le_mul_right (htail _ (by positivity)) _
    _ = _ := by ring

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma capSum_eq_of_max {L : Length} (m : ℕ) {r R : ℝ} (hr : 0 ≤ r)
    (ω : ConfigurationPath 1 L) (hmax : ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R) :
    capSum m r ((1+R)^3) ω=∑j : Fin m,cubicCost r (meshSegment j ω) := by
  unfold capSum
  apply Finset.sum_congr rfl
  intro j _
  apply min_eq_left
  unfold cubicCost
  exact pow_le_pow_left₀ (by linarith [diameterRatio_nonneg hr (meshSegment j ω)]) (by linarith [hmax j]) 3

lemma mesh_irregular_sub {L : Length} {m : ℕ} {r R : ℝ} (hr : 0 ≤ r) :
    {ω : ConfigurationPath 1 L | ¬MeshRegular m r R (meanCost+1) ω} ⊆
      meshEvent m {ω | R < diameterRatio r ω} ∪
      {ω | (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) ω} := by
  intro ω hω
  by_cases hmax : ∀j : Fin m, diameterRatio r (meshSegment j ω) ≤ R
  · right
    change (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) ω
    rw [capSum_eq_of_max m hr ω hmax]
    have hn : (meanCost+1)*(m:ℝ) < ∑j : Fin m,cubicCost r (meshSegment j ω) := by
      exact lt_of_not_ge (fun h ↦ hω ⟨hmax,h⟩)
    exact hn.le
  · left
    simpa only [meshEvent,Set.mem_ofPred_eq,not_forall,not_le] using hmax

lemma free_mesh_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0 ≤ R → wiener {w | R ≤ ‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ ≤ r^2) (hR : 0 ≤ R)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬MeshRegular m r R (meanCost+1) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+R)^3))) := by
  have hB : 0 < (1+R)^3 := by positivity
  have hp := meshEvent_free_bound (L:=L) m hm
    (measurableSet_lt measurable_const (diameterRatio_continuous L r).measurable) hτ
    (3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))
    (fun Y ↦ free_diameterRatio_tail htail hr hτr hR Y) X
  calc
    _ ≤ coordinateWiener 1 ({w | freeTrajectory 1 L ((m:ℝ)*τ) w X ∈ meshEvent m {ω | R < diameterRatio r ω}} ∪
      {w | (meanCost+1)*(m:ℝ) ≤ capSum m r ((1+R)^3) (freeTrajectory 1 L ((m:ℝ)*τ) w X)}) :=
      measure_mono (fun w hw ↦ mesh_irregular_sub hr.le hw)
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hp (mesh_cap_tail hr hτ hτr hB m hm X))

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma free_split_lintegral {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (F : ConfigurationPath 1 L × ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    (X : Configuration 1 L) :
    ∫⁻w,F (configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X),
      configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X)) ∂coordinateWiener 1 =
    ∫⁻w₁,∫⁻w₂,F (freeTrajectory 1 L s w₁ X,
      freeTrajectory 1 L t w₂ (freeTrajectory 1 L s w₁ X 1)) ∂coordinateWiener 1 ∂coordinateWiener 1 := by
  let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun p ↦
    F (freeTrajectory 1 L s p.1 X,freeTrajectory 1 L t p.2 (freeTrajectory 1 L s p.1 X 1))
  have hG : Measurable G := hF.comp (split_fixedTrajectory_measurable 1 L s t X)
  calc
    _ = ∫⁻w,G (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
        fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener 1 :=
      lintegral_congr (fun w ↦ by rw [split_fixedTrajectory])
    _ = ∫⁻p,G p ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
      (coordinateSplit_preserving 1 (splitTime s t hs ht) (splitTime_pos _ _ _ _)
        (splitTime_lt_one _ _ _ _)).lintegral_comp hG
    _ = _ := lintegral_prod _ hG.aemeasurable

lemma free_prefix_bound {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L s w X) ∂coordinateWiener 1 ≤ p)
    (X : Configuration 1 L) :
    ∫⁻w,F (configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X)) ∂coordinateWiener 1 ≤ p := by
  have h := free_split_lintegral hs ht (fun p ↦ F p.1) (hF.comp measurable_fst) X
  dsimp only at h
  simp only [lintegral_const,measure_univ,mul_one] at h
  rw [h]
  exact hp X

lemma free_suffix_bound {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤ p)
    (X : Configuration 1 L) :
    ∫⁻w,F (configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X)) ∂coordinateWiener 1 ≤ p := by
  have h := free_split_lintegral hs ht (fun p ↦ F p.2) (hF.comp measurable_snd) X
  dsimp only at h
  rw [h]
  calc
    _ ≤ ∫⁻w₁,p ∂coordinateWiener 1 := lintegral_mono (fun w ↦ hp _)
    _ = p := by simp

lemma free_prefix_event {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L,coordinateWiener 1 {w | freeTrajectory 1 L s w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} ≤ p := by
  apply (le_of_eq ?_).trans (free_prefix_bound hs ht (E.indicator (fun _ ↦ 1))
    (measurable_const.indicator hE) p (fun Y ↦ ?_) X)
  · have he : MeasurableSet {w | configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} :=
      hE.preimage (((configurationPrefix_continuous 1 L _).comp
        ((freeTrajectory_continuous 1 L (s+t)).comp (continuous_id.prodMk continuous_const))).measurable)
    change coordinateWiener 1 _=∫⁻w,({w | configurationPrefix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1
    rw [lintegral_indicator_const he,one_mul]
  · have he : MeasurableSet {w | freeTrajectory 1 L s w Y ∈ E} := hE.preimage
      ((freeTrajectory_continuous 1 L s).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻w,({w | freeTrajectory 1 L s w Y ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const he,one_mul] using hp Y

lemma free_suffix_event {L : Length} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) (p : ℝ≥0∞)
    (hp : ∀ X : Configuration 1 L,coordinateWiener 1 {w | freeTrajectory 1 L t w X ∈ E} ≤ p)
    (X : Configuration 1 L) :
    coordinateWiener 1 {w | configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} ≤ p := by
  apply (le_of_eq ?_).trans (free_suffix_bound hs ht (E.indicator (fun _ ↦ 1))
    (measurable_const.indicator hE) p (fun Y ↦ ?_) X)
  · have he : MeasurableSet {w | configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E} :=
      hE.preimage (((configurationSuffix_continuous 1 L _).comp
        ((freeTrajectory_continuous 1 L (s+t)).comp (continuous_id.prodMk continuous_const))).measurable)
    change coordinateWiener 1 _=∫⁻w,({w | configurationSuffix 1 L (splitTime s t hs ht) (freeTrajectory 1 L (s+t) w X) ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1
    rw [lintegral_indicator_const he,one_mul]
  · have he : MeasurableSet {w | freeTrajectory 1 L t w Y ∈ E} := hE.preimage
      ((freeTrajectory_continuous 1 L t).comp (continuous_id.prodMk continuous_const)).measurable
    change ∫⁻w,({w | freeTrajectory 1 L t w Y ∈ E}.indicator (fun _ ↦ (1:ℝ≥0∞))) w ∂coordinateWiener 1 ≤ p
    simpa only [lintegral_indicator_const he,one_mul] using hp Y

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma diameterRatio_reverse {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    diameterRatio r (reverseConfigurationPath 1 L ω)=diameterRatio r ω := by
  unfold diameterRatio
  rw [intervalDiameter_reverse]
  simp [reverseTime]

lemma meshRegular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (ω : ConfigurationPath 1 L) :
    MeshRegular m r R C (reverseConfigurationPath 1 L ω) ↔ MeshRegular m r R C ω := by
  unfold MeshRegular
  rw [mesh_sum_reverse _ (cubicCost_reverse r)]
  simp only [meshSegment_reverse,diameterRatio_reverse]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨fun j ↦ by simpa using h j.rev,h'⟩
  · rintro ⟨h,h'⟩
    exact ⟨fun j ↦ h j.rev,h'⟩

lemma endpointRegular_reverse {L : Length} (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    EndpointRegular u S (reverseConfigurationPath 1 L ω) ↔ EndpointRegular u S ω := by
  unfold EndpointRegular
  rw [intervalDiameter_reverse,intervalDiameter_reverse,reverseTime_reverse]
  simpa only [reverseTime_zero,reverseTime_one] using (and_comm : (_ ∧ _) ↔ (_ ∧ _))

lemma regular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    Regular m r R C u S (reverseConfigurationPath 1 L ω) ↔ Regular m r R C u S ω := by
  exact and_congr (meshRegular_reverse m r R C ω) (endpointRegular_reverse u S ω)

lemma interval_prefix {L : Length} (u : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter 0 u ω=intervalDiameter 0 1 (configurationPrefix 1 L u ω) := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  change torusDistance L (ω (intervalTime 0 u p.1) 0) (ω (intervalTime 0 u p.2) 0)=
    torusDistance L (ω (prefixTime u (intervalTime 0 1 p.1)) 0) (ω (prefixTime u (intervalTime 0 1 p.2)) 0)
  have he (s : Time) : intervalTime 0 u s=prefixTime u (intervalTime 0 1 s) := by
    apply Subtype.ext
    simp [intervalTime,prefixTime,mul_comm]
  rw [he,he]

lemma interval_suffix {L : Length} (u : Time) (ω : ConfigurationPath 1 L) :
    intervalDiameter u 1 ω=intervalDiameter 0 1 (configurationSuffix 1 L u ω) := by
  apply congrArg norm
  apply ContinuousMap.ext
  intro p
  change torusDistance L (ω (intervalTime u 1 p.1) 0) (ω (intervalTime u 1 p.2) 0)=
    torusDistance L (ω (suffixTime u (intervalTime 0 1 p.1)) 0) (ω (suffixTime u (intervalTime 0 1 p.2)) 0)
  have he (s : Time) : intervalTime u 1 s=suffixTime u (intervalTime 0 1 s) := by
    apply Subtype.ext
    change (1-(s:ℝ))*(u:ℝ)+(s:ℝ)*1 = (u:ℝ)+(1-(u:ℝ))*((1-(s:ℝ))*0+(s:ℝ)*1)
    ring
  rw [he,he]

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CenteredCell
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centeredCount_measurable {n : ℕ} (L : Length) (c : Torus L) :
    Measurable (centeredCount (n:=n) L c) := by
  classical
  unfold centeredCount
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((centeredCell_measurable L c).preimage (measurable_pi_apply i))
    measurable_const measurable_const

end
end HardSphere.CellOrbital

namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centeredCell_image {L : Length} (hL : 1 ≤ L.val) (c x : Torus L) :
    x∈centeredCell L c ↔ ∀ j, ∃ t∈Ico (-1/2:ℝ) (1/2), (t : AddCircle L.val)=x j-c j := by
  constructor
  · intro hx j
    exact ⟨_,hx j,AddCircle.coe_equivIco⟩
  · intro hx j
    obtain ⟨t,ht,he⟩ := hx j
    have ht' : t∈Ico (-L.val/2) (-L.val/2+L.val) := by constructor <;> linarith [ht.1,ht.2]
    rw [← he,AddCircle.equivIco_coe_eq ht']
    exact ht

lemma fin_circle_dist {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) {v w : Fin K} (hvw : v≠w) :
    1 ≤ dist ((v:ℝ) : AddCircle L.val) ((w:ℝ) : AddCircle L.val) := by
  have hi (v : Fin K) : (v:ℝ)∈Ico (0:ℝ) (0+L.val) := by
    constructor
    · positivity
    · simpa only [zero_add,hL] using (show (v:ℝ)<(K:ℝ) by exact_mod_cast v.isLt)
  have hne : ((v:ℝ):AddCircle L.val)≠((w:ℝ):AddCircle L.val) := by
    intro he
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hi v) (hi w)).mp he
    exact hvw (Fin.ext (by exact_mod_cast he'))
  let z : ℤ := (v.val:ℤ)-(w.val:ℤ)-round (L.val⁻¹*((v:ℝ)-(w:ℝ)))*(K:ℤ)
  have hd : dist ((v:ℝ):AddCircle L.val) ((w:ℝ):AddCircle L.val)=|(z:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    dsimp [z]
    push_cast
    rw [hL]
  have hz : z≠0 := by
    intro hz
    apply hne
    apply dist_eq_zero.mp
    rw [hd,hz,Int.cast_zero,abs_zero]
  have ha : (1:ℤ)≤|z| := by
    have hh : 0 < |z| := abs_pos.mpr hz
    omega
  rw [hd,← Int.cast_abs]
  exact_mod_cast ha

end
end HardSphere.CellOrbital

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CellPartition
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace HardSphere.CellOrbital

lemma gridHome_mem {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K) (x : Torus L) :
    x∈centeredCell L (gridCenter L (gridHome hL x)) := by
  apply (centeredCell_image (by rw [hL]; exact_mod_cast hK) _ _).mpr
  intro j
  let z := (AddCircle.equivIco L.val 0) (x j+(1/2:ℝ))
  have hz0 : 0≤z.val := z.property.1
  let n : ℕ := ⌊z.val⌋₊
  refine ⟨z.val-(n:ℝ)-1/2,⟨?_,?_⟩,?_⟩
  · linarith [Nat.floor_le hz0]
  · have hh := Nat.lt_floor_add_one z.val
    dsimp [n]
    linarith
  · have he : (z.val : AddCircle L.val)=x j+((1/2:ℝ):AddCircle L.val) := AddCircle.coe_equivIco
    change ((z.val-(n:ℝ)-1/2:ℝ):AddCircle L.val)=x j-((n:ℝ):AddCircle L.val)
    simp only [QuotientAddGroup.mk_sub]
    rw [he]
    abel

lemma centeredCell_disjoint {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {v w : Fin 3→Fin K} (hvw : v≠w) : Disjoint (centeredCell L (gridCenter L v)) (centeredCell L (gridCenter L w)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,hj⟩ : ∃j,v j≠w j := by
    by_contra h
    push Not at h
    exact hvw (funext h)
  have h1 : 1≤L.val := by rw [hL]; exact_mod_cast hK
  obtain ⟨s,hs,hes⟩ := (centeredCell_image h1 _ _).mp hx j
  obtain ⟨t,ht,het⟩ := (centeredCell_image h1 _ _).mp hy j
  have he : gridCenter L v j-gridCenter L w j=((t-s:ℝ):AddCircle L.val) := by
    rw [QuotientAddGroup.mk_sub,het,hes]
    abel
  have ha : |t-s|<1 := by rw [abs_lt]; constructor <;> linarith [ht.1,ht.2,hs.1,hs.2]
  have hd : dist (gridCenter L v j) (gridCenter L w j)<1 := by
    rw [dist_eq_norm,he]
    exact lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm (m:=t-s)) (by simpa only [Real.norm_eq_abs] using ha)
  exact (not_lt_of_ge (fin_circle_dist hL hj)) hd

lemma gridHome_eq_iff {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (x : Torus L) (v : Fin 3→Fin K) : gridHome hL x=v ↔ x∈centeredCell L (gridCenter L v) := by
  constructor
  · intro h; exact h ▸ gridHome_mem hL hK x
  · intro hx
    by_contra h
    exact Set.disjoint_left.mp (centeredCell_disjoint hL hK h) (gridHome_mem hL hK x) hx

end HardSphere.CellOrbital

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_Allocation
attribute [-instance] _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Sampling.siteAllocationKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_large (E : Finset I) (m : ℕ) (h : m≤E.card)
    [Nonempty (Fin m↪E)] :
    allocationPMF E m=(PMF.uniformOfFintype (Fin m↪E)).map (fun f ↦ some (f.trans (Function.Embedding.subtype _))) := by
  simp [allocationPMF,h]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_small (E : Finset I) (m : ℕ) (h : ¬m≤E.card) :
    allocationPMF E m=PMF.pure none := by simp [allocationPMF,h]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_support (E : Finset I) (m : ℕ) (a : Allocation m I)
    (h : a∈(allocationPMF E m).support) :
    ∀f,a=some f→∀k,f k∈E := by
  classical
  by_cases hm : m≤E.card
  · have : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hm)
    rw [allocationPMF_large E m hm,PMF.support_map] at h
    obtain ⟨g,_,rfl⟩ := h
    intro f hf k
    have he : g.trans (Function.Embedding.subtype _)=f := Option.some.inj hf
    exact he ▸ (g k).property
  · rw [allocationPMF_small E m hm,PMF.support_pure] at h
    have ha : a=none := h
    simp only [ha,reduceCtorEq,false_implies,implies_true]

omit [Fintype I] [DecidableEq I] in
lemma allocated_group_uniform (E : Finset I) (m q : ℕ) (h : m≤E.card)
    (group : Fin q↪Fin m) :
    (allocationPMF E m).map (Option.map (fun f ↦ group.trans f))=allocationPMF E q := by
  classical
  have hqm : q ≤ m := by simpa using Fintype.card_le_of_embedding group
  have hq : q≤E.card := hqm.trans h
  have : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  have : Nonempty (Fin q↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hq)
  rw [allocationPMF_large E m h,allocationPMF_large E q hq,PMF.map_comp]
  have hu := congrArg (fun P : PMF (Fin q↪E) ↦ P.map (fun f ↦ some (f.trans (Function.Embedding.subtype _))))
    (embedding_restriction_uniform (V:=E) group)
  rw [PMF.map_comp] at hu
  exact hu

lemma allocation_half_bad (E B : Finset I) (m : ℕ) (hE : 2*m≤E.card)
    (hB : 10*(E∩B).card≤E.card) :
    (allocationPMF E (2*m)).toMeasure
      {a | ∃f,a=some f ∧ m≤(Finset.univ.filter (fun k ↦ f k∈B)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^m) := by
  classical
  have : Nonempty (Fin (2*m)↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hE)
  let : MeasurableSpace (Fin (2*m)↪E) := ⊤
  let : MeasurableSingletonClass (Fin (2*m)↪E) := ⟨fun _ ↦ trivial⟩
  by_cases hempty : E.Nonempty
  · have : Nonempty E := hempty.to_subtype
    rw [allocationPMF_large E (2*m) hE,←PMF.toMeasure_map _ _ (measurable_of_countable _)]
    rw [Measure.map_apply (measurable_of_countable _) (by exact MeasurableSet.of_discrete)]
    let bad : Set E := {i | i.val∈B}
    have hc : Fintype.card bad=(E∩B).card := by
      let equiv : bad ≃ (E∩B : Finset I) :=
        { toFun := fun i ↦ ⟨i.val.val,Finset.mem_inter.mpr ⟨i.val.property,i.property⟩⟩
          invFun := fun i ↦ ⟨⟨i.val,(Finset.mem_inter.mp i.property).1⟩,(Finset.mem_inter.mp i.property).2⟩
          left_inv := fun i ↦ by cases i; rfl
          right_inv := fun i ↦ by cases i; rfl }
      exact (Fintype.card_congr equiv).trans (Fintype.card_coe (E∩B))
    have hb : (Nat.card bad:ℝ)≤(Fintype.card E:ℝ)/10 := by
      rw [Nat.card_eq_fintype_card,hc,Fintype.card_coe]
      have hb' : (10:ℝ)*((E∩B).card:ℝ)≤(E.card:ℝ) := by exact_mod_cast hB
      linarith
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (by exact MeasurableSet.of_discrete)]
    have hset : (fun f : Fin (2*m)↪E ↦ some (f.trans (Function.Embedding.subtype _))) ⁻¹'
        {a : Allocation (2*m) I | ∃f,a=some f ∧ m≤(Finset.univ.filter (fun k ↦ f k∈B)).card}=
        {f : Fin (2*m)↪E | m≤(Finset.univ.filter (fun k ↦ f k∈bad)).card} := by
      ext f
      simp [bad]
    rw [hset]
    have he : ENNReal.ofReal ((2/5:ℝ)^m)=(2/5:ℝ≥0∞)^m := by
      rw [ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [he]
    convert uniform_half_bad (V:=E) m bad hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext f
    simp only [Set.mem_ofPred_eq]
    apply iff_of_eq
    congr 1
    congr 1
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  · have hz : E=∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hm : m=0 := by simp [hz] at hE; omega
    subst m
    simp only [pow_zero,ENNReal.ofReal_one]
    exact prob_le_one

end HardSphere.Sampling

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianMixture
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking
lemma center_zero (β : C(Time,ℝ)) : center β 0=0 := by simp [center,linearPath]
lemma center_one (β : C(Time,ℝ)) : center β 1=0 := by simp [center,linearPath]

lemma pinned_leg_zero (t : ℝ) (y u : Point) (β : Noise) : leg t y u (pinned β) 0=y := by
  ext j
  simp [leg,mean,pinned,center_zero]
lemma pinned_leg_one (t : ℝ) (y u : Point) (β : Noise) : leg t y u (pinned β) 1=u := by
  ext j
  simp [leg,mean,pinned,center_one]

lemma trial_zero (t : ℝ) (y z u : Point) (β : Noise×Noise) : trialPath t y z u β 0=y := by
  have hl : leftTime 0=0 := by ext; simp [leftTime]
  have hr : reverseTime (rightTime 0)=1 := by ext; simp [rightTime,reverseTime]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_zero,pinned_leg_one,add_sub_cancel_right]
lemma trial_one (t : ℝ) (y z u : Point) (β : Noise×Noise) : trialPath t y z u β 1=z := by
  have hl : leftTime 1=1 := by ext; norm_num [leftTime]
  have hr : reverseTime (rightTime 1)=0 := by ext; norm_num [rightTime,reverseTime]
  simp only [trialPath,ContinuousMap.coe_mk,hl,hr,pinned_leg_zero,pinned_leg_one]
  abel

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialCutoff
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trialConfined_measurable (L : Length) (v : Point) : MeasurableSet {f | TrialConfined L v f} := by
  have he : {f | TrialConfined L v f}=⋂s : Time,{f : C(Time,Point) | ‖f s-v‖≤10 ∧ torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10} := by ext f; simp [TrialConfined]
  rw [he]
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro s
  change IsClosed ({f : C(Time,Point) | ‖f s-v‖≤10} ∩ {f | torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10})
  apply IsClosed.inter
  · exact isClosed_le ((continuous_eval_const s).sub continuous_const).norm continuous_const
  · apply isClosed_le _ continuous_const
    unfold torusDistance projectPoint
    fun_prop

lemma trialCutoff_measurable (L : Length) (n : ℕ) (r R C : ℝ) (w : Time) (S : ℝ) (v : Point) :
    MeasurableSet {f | TrialCutoff L n r R C w S v f} :=
  ((regular_measurable (n+n) r R C (prefixTime midpointTime w) S).preimage (projectCurve_continuous L).measurable).inter (trialConfined_measurable L v)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSuccess
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma trialCollision_closed {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    IsClosed {f | TrialCollision r ω f} := by
  let E : Set (C(Time,Point)×Time) := {p | torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0) ≤ r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f := fun p : C(Time,Point)×Time ↦
      (projectPoint L (p.1 p.2),ω p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : C(Time,Point)×Time ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
      fun_prop
    · exact (continuous_apply 0).comp (ω.continuous.comp continuous_snd)
  convert isClosedMap_fst_of_compactSpace E hE using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(f,s),hs,rfl⟩,fun ⟨⟨g,s⟩,hs,hg⟩ ↦ by
    change g=f at hg
    subst g
    exact ⟨s,hs⟩⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma fixedEndpoints_measurable (y z : Point) : MeasurableSet (fixedEndpoints y z) :=
  (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
    (measurableSet_eq_fun (continuous_eval_const 1).measurable measurable_const)

lemma trial_fixedEndpoints (t : ℝ) (y z u : Point) :
    ∀ᵐf ∂trialKernel t y z u,f∈fixedEndpoints y z := by
  rw [trialKernel_apply]
  apply (ae_map_iff ((trialPath_continuous t y z).measurable.comp
    (measurable_const.prodMk measurable_id)).aemeasurable (fixedEndpoints_measurable y z)).mpr
  exact ae_of_all _ (fun β ↦ ⟨trial_zero t y z u β,trial_one t y z u β⟩)

lemma measure_inter_ae_full {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S T : Set X) (hT : ∀ᵐx ∂μ,x∈T) : μ (S∩T)=μ S := by
  apply measure_congr
  filter_upwards [hT] with x hx
  apply propext
  change (x∈S ∧ x∈T) ↔ x∈S
  simp only [hx,and_true]

lemma trialKernel_pin (t : ℝ) (y z u : Point) (S : Set C(Time,Point)) :
    trialKernel t y z u (S∩fixedEndpoints y z)=trialKernel t y z u S :=
  measure_inter_ae_full _ _ _ (trial_fixedEndpoints t y z u)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCloseLabelsMeasurable
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

variable {n : ℕ} [Nontrivial (Fin n)]

attribute [local irreducible] torusDistance nearestParticleDistance

lemma localCloseLabels_measurable (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun X : Configuration n L ↦ ((localCloseLabels L s v X).card:ℝ)) := by
  classical
  simp only [localCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun X : Configuration n L ↦ torusDistance L (X i) v) :=
    (torusDistance_continuous_pair L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration n L ↦ v)))
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter
    (measurableSet_le (nearestParticleDistance_continuous L i).measurable measurable_const))
    measurable_const measurable_const

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_CloseTailBaseTendsto
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma smallness_of_large_density {n : ℕ} (L : Length) {D α αmax : ℝ}
    (hDeq : D=(n:ℝ)/L.val^3) (hD : 1≤D) (hα : 0≤α) (hαmax : α≤αmax)
    (hlarge : 2*(2*Real.pi*αmax)^3≤D) :
    (n:ℝ)*(2*Real.pi*(α/D))^3≤L.val^3/2 := by
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hL3 : 0<L.val^3 := pow_pos L.property _
  have hn : (n:ℝ)=D*L.val^3 := ((eq_div_iff hL3.ne').mp hDeq).symm
  have halpha : (2*Real.pi*α)^3≤(2*Real.pi*αmax)^3 := by gcongr
  have hDsq : D≤D^2 := by nlinarith only [mul_le_mul_of_nonneg_left hD hDpos.le]
  have hratio : (2*Real.pi*α)^3/D^2≤1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hDpos)).mpr
    nlinarith only [halpha,hlarge,hDsq]
  calc
    _ = L.val^3*((2*Real.pi*α)^3/D^2) := by rw [hn]; field_simp
    _ ≤ L.val^3*(1/2) := mul_le_mul_of_nonneg_left hratio hL3.le
    _ = _ := by ring

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SiteCube
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open MeasureTheory Set Filter HardSphere.Lattice

lemma unitCenter_siteCube {K : ℕ} [NeZero K] (L : Length) (v : DiscreteTorus K) :
    unitCenter L (siteCube v) = siteCenter L v := by
  funext j
  fin_cases j <;> rfl

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ShiftInteracting
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.FreeVisits

lemma visitorCount_sum {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath n L) :
    (∑v∈A,visitorCount L c E v ω)=defectiveTotalVisits L c A E ω := by
  classical
  simp only [visitorCount,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : onePathAt i ω∈E
  · simp only [hi,true_and,pathVisitedSites,ite_eq_left,Finset.card_filter]
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero,pathVisitedSites]

lemma visitorCount_measurable {n K : ℕ} (L : Length) (c : Torus L) {E : Set (ConfigurationPath 1 L)}
    (hE : MeasurableSet E) (v : DiscreteTorus K) : Measurable (visitorCount (n:=n) L c E v) := by
  classical
  have he : visitorCount (n:=n) L c E v=(fun ω ↦ ∑i : Fin n, if onePathAt i ω∈E ∧ pathVisitsBall L 12 (center L c v) i ω then (1:ℕ) else 0) := by
    funext ω
    simp only [visitorCount,Finset.card_filter]
  rw [he]
  apply Finset.measurable_fun_sum
  intro i _
  have hi : MeasurableSet {ω : ConfigurationPath n L | onePathAt i ω∈E} := hE.preimage (onePathAt_continuous i).measurable
  exact measurable_const.ite (hi.inter (pathVisitsBall_isClosed L 12 (center L c v) i).measurableSet) measurable_const

lemma defectiveTotalVisits_measurable {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E) : Measurable (defectiveTotalVisits (n:=n) L c A E) := by
  have he : defectiveTotalVisits (n:=n) L c A E=fun ω ↦ ∑v∈A,visitorCount L c E v ω := by
    funext ω; exact (visitorCount_sum L c A E ω).symm
  rw [he]
  exact Finset.measurable_fun_sum _ (fun v _ ↦ visitorCount_measurable L c hE v)

lemma joint_visitor_sum {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    (E : Set (ConfigurationPath 1 L)) {H : ℝ} {ω : ConfigurationPath n L}
    (h : ∀v∈A,H≤(visitorCount L c E v ω:ℝ)) :
    H*(A.card:ℝ)≤(defectiveTotalVisits L c A E ω:ℝ) := by
  rw [←visitorCount_sum L c A E ω,Nat.cast_sum]
  have hs := Finset.sum_le_sum h
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hs

lemma joint_visitors_markov {n K : ℕ} (L : Length) (c : Torus L) (A : Finset (DiscreteTorus K))
    {E : Set (ConfigurationPath 1 L)} (hE : MeasurableSet E)
    (μ : Measure (ConfigurationPath n L)) {η H Q : ℝ} (hη : 0≤η)
    (hmgf : (∫⁻ω,ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ))) ∂μ)≤
      ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))) :
    μ {ω | ∀v∈A,H≤(visitorCount L c E v ω:ℝ)}≤ENNReal.ofReal (Real.exp ((Q-η*H)*(A.card:ℝ))) := by
  let F := fun ω : ConfigurationPath n L ↦ ENNReal.ofReal (Real.exp (η*(defectiveTotalVisits L c A E ω:ℝ)))
  have hc : Measurable (fun k : ℕ ↦ (k:ℝ)) := measurable_of_countable _
  have hF : Measurable F := ((measurable_const.mul (hc.comp (defectiveTotalVisits_measurable L c A hE))).exp).ennreal_ofReal
  have hp : ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≠0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm := meas_ge_le_lintegral_div (μ:=μ) hF.aemeasurable hp ENNReal.ofReal_ne_top
  calc
    _ ≤ μ {ω | ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ))))≤F ω} := by
      apply measure_mono
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (joint_visitor_sum L c A E hω) hη
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (Real.exp (Q*(A.card:ℝ)))/ENNReal.ofReal (Real.exp (η*(H*(A.card:ℝ)))) := ENNReal.div_le_div_right hmgf _
    _ = _ := by
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.ShiftVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAlignment
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open Classical
namespace HardSphere.Groups
open CellOrbital BathSlice HardSphere.Lattice ShiftVisits

lemma gridSite_injective {K : ℕ} [NeZero K] : Function.Injective (gridSite (K:=K)) := by
  intro v w h
  funext j
  apply Fin.ext
  have hh := congrArg (fun f : DiscreteTorus K ↦ (f j).val) h
  simpa only [gridSite,ZMod.val_natCast_of_lt (v j).isLt,ZMod.val_natCast_of_lt (w j).isLt] using hh

lemma siteCube_gridSite {K : ℕ} [NeZero K] (v : Fin 3→Fin K) : siteCube (gridSite v)=gridCube v := by
  apply Prod.ext
  · apply Fin.ext
    exact ZMod.val_natCast_of_lt (v 0).isLt
  · apply Prod.ext <;> apply Fin.ext
    · exact ZMod.val_natCast_of_lt (v 1).isLt
    · exact ZMod.val_natCast_of_lt (v 2).isLt

lemma shifted_unitCenter {K : ℕ} (L : Length) (v : Fin 3→Fin K) :
    unitCenter L (gridCube v)+gridShift L=gridCenter L v := by
  funext j
  fin_cases j <;> change ((((_:ℝ)+1/2:ℝ):AddCircle L.val)+((-1/2:ℝ):AddCircle L.val))=(_ : AddCircle L.val)
  all_goals
    rw [←AddCircle.coe_add]
    congr 1
    simp only [gridCube]
    ring_nf
    rfl

lemma shifted_siteCenter {K : ℕ} [NeZero K] (L : Length) (v : Fin 3→Fin K) :
    ShiftVisits.center L (gridShift L) (gridSite v)=gridCenter L v := by
  rw [ShiftVisits.center,←unitCenter_siteCube,siteCube_gridSite]
  exact shifted_unitCenter L v

lemma grid_visitorCount {n K : ℕ} [NeZero K] (L : Length) (E : Set (ConfigurationPath 1 L))
    (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    ShiftVisits.visitorCount L (gridShift L) E (gridSite v) ω=
      (Finset.univ.filter (fun i : Fin n ↦ onePathAt i ω∈E ∧ pathVisitsBall L 12 (gridCenter L v) i ω)).card := by
  classical
  simp only [ShiftVisits.visitorCount,shifted_siteCenter]

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_GridTailTransfer
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice

lemma joint_event_image {W V U : Type*} [MeasurableSpace W] [DecidableEq U]
    (μ : Measure W) (f : V→U) (P : U→W→Prop) (A : Finset V) :
    μ {ω | ∀v∈A,P (f v) ω}=μ {ω | ∀u∈A.image f,P u ω} := by
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq,Finset.mem_image,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]

lemma grid_visitors_eq {n K : ℕ} [NeZero K] (L : Length)
    (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    ShiftVisits.visitorCount L (gridShift L) Set.univ (gridSite v) ω=(visitors (gridCenter L v) ω).card := by
  classical
  rw [grid_visitorCount]
  apply congrArg Finset.card
  ext i
  simp [visitors]

lemma grid_longVisitors_eq {n K : ℕ} [NeZero K] (L : Length)
    (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    ShiftVisits.visitorCount L (gridShift L) {p | 1 < intervalDiameter 0 1 p} (gridSite v) ω=
      (longVisitors (gridCenter L v) ω).card := by
  classical
  rw [grid_visitorCount]
  apply congrArg Finset.card
  ext i
  simp [longVisitors,and_comm]

lemma grid_nonregular_iff {n K : ℕ} [NeZero K] (L : Length)
    (m : ℕ) (r R C S : ℝ) (u : Time) (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    (¬∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)) ↔
    1≤(ShiftVisits.visitorCount L (gridShift L) {p | ¬Regular m r R C u S p} (gridSite v) ω:ℝ) := by
  classical
  rw [grid_visitorCount]
  have hcast (k : ℕ) : (1:ℝ)≤(k:ℝ) ↔ 1≤k := by exact_mod_cast Iff.rfl
  rw [hcast,Finset.one_le_card]
  change (¬∀i, _ → _) ↔ ∃i, i∈_
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq]
  push Not
  exact exists_congr (fun i ↦ and_comm)

lemma ofReal_power_tail {x q : ℝ} (hx : 0≤x) (hq : 0≤q) (h : x≤q^6) (n : ℕ) :
    ENNReal.ofReal (x^n)≤(ENNReal.ofReal q)^(6*n) := by
  rw [pow_mul,←ENNReal.ofReal_pow hq,←ENNReal.ofReal_pow (pow_nonneg hq _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hx h n)

lemma exp_power_tail {x q : ℝ} (hq : 0≤q) (h : Real.exp x≤q^6) (n : ℕ) :
    ENNReal.ofReal (Real.exp (x*(n:ℝ)))≤(ENNReal.ofReal q)^(6*n) := by
  rw [mul_comm x (n:ℝ),Real.exp_nat_mul]
  exact ofReal_power_tail (Real.exp_pos x).le hq h n

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateMeasurable
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice

lemma regular_mono_constants {L : Length} {m : ℕ} {r R C R' C' S : ℝ} {u : Time}
    {ω : ConfigurationPath 1 L} (hR : R≤R') (hC : C≤C')
    (h : Regular m r R C u S ω) : Regular m r R' C' u S ω := by
  refine ⟨⟨fun j ↦ (h.1.1 j).trans hR,?_⟩,h.2⟩
  exact h.1.2.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))

lemma certificate_mono_constants {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    {m : ℕ} {r R C R' C' S s₀ ell θ H D : ℝ} {u : Time} {v : Fin 3→Fin K}
    {ω : ConfigurationPath N L} (hR : R≤R') (hC : C≤C')
    (h : Certificate m r R C S s₀ ell θ H D u v ω) :
    Certificate m r R' C' S s₀ ell θ H D u v ω :=
  ⟨h.low,h.closeY,h.closeZ,h.visit,fun i hi ↦ regular_mono_constants hR hC (h.regular i hi),h.long⟩

lemma certificate_measurable {N K : ℕ} [Nontrivial (Fin N)] [NeZero K] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K) :
    MeasurableSet {ω : ConfigurationPath N L | Certificate m r R C S s₀ ell θ H D u v ω} := by
  classical
  have hc : Measurable (fun n : ℕ ↦ (n:ℝ)) := measurable_of_countable _
  have hlo : MeasurableSet {ω : ConfigurationPath N L | ell*D≤(centeredCount L (gridCenter L v) (ω 0):ℝ)} :=
    measurableSet_le measurable_const (hc.comp
      ((centeredCount_measurable L (gridCenter L v)).comp (continuous_eval_const 0).measurable))
  have hY : MeasurableSet {ω : ConfigurationPath N L | ((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ)<θ*D} :=
    measurableSet_lt ((localCloseLabels_measurable L s₀ (gridCenter L v)).comp (continuous_eval_const 0).measurable) measurable_const
  have hZ : MeasurableSet {ω : ConfigurationPath N L | ((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ)<θ*D} :=
    measurableSet_lt ((localCloseLabels_measurable L s₀ (gridCenter L v)).comp (continuous_eval_const 1).measurable) measurable_const
  have hv : Measurable (fun ω : ConfigurationPath N L ↦ (visitors (gridCenter L v) ω).card) := by
    have he : (fun ω : ConfigurationPath N L ↦ (visitors (gridCenter L v) ω).card) =
        ShiftVisits.visitorCount L (gridShift L) Set.univ (gridSite v) :=
      funext fun ω ↦ (grid_visitors_eq L v ω).symm
    rw [he]
    exact ShiftVisits.visitorCount_measurable (n:=N) L (gridShift L) MeasurableSet.univ (gridSite v)
  have ht : Measurable (fun ω : ConfigurationPath N L ↦ (longVisitors (gridCenter L v) ω).card) := by
    have he : (fun ω : ConfigurationPath N L ↦ (longVisitors (gridCenter L v) ω).card) =
        ShiftVisits.visitorCount L (gridShift L) {p | 1 < intervalDiameter 0 1 p} (gridSite v) :=
      funext fun ω ↦ (grid_longVisitors_eq L v ω).symm
    rw [he]
    exact ShiftVisits.visitorCount_measurable (n:=N) L (gridShift L)
      (measurableSet_lt measurable_const (intervalDiameter_continuous L 0 1).measurable) (gridSite v)
  have hreg : MeasurableSet {ω : ConfigurationPath N L | ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have he : {ω : ConfigurationPath N L | pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)}=
      {ω | pathVisitsBall L 12 (gridCenter L v) i ω}ᶜ∪{ω | Regular m r R C u S (onePathAt i ω)} := by ext ω; simp [imp_iff_not_or]
    rw [he]
    exact (pathVisitsBall_isClosed L 12 (gridCenter L v) i).measurableSet.compl.union
      ((regular_measurable m r R C u S).preimage (onePathAt_continuous i).measurable)
  have he : {ω : ConfigurationPath N L | Certificate m r R C S s₀ ell θ H D u v ω}=
      {ω | ell*D≤(centeredCount L (gridCenter L v) (ω 0):ℝ)} ∩
      ({ω | ((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ)<θ*D} ∩
      ({ω | ((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ)<θ*D} ∩
      ({ω | ((visitors (gridCenter L v) ω).card:ℝ)≤H*D} ∩
      ({ω | ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)} ∩
      {ω | ((longVisitors (gridCenter L v) ω).card:ℝ)<θ*D})))) := by
    ext ω
    constructor
    · exact fun h ↦ ⟨h.low,h.closeY,h.closeZ,h.visit,h.regular,h.long⟩
    · exact fun h ↦ ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  rw [he]
  exact hlo.inter (hY.inter (hZ.inter ((measurableSet_le (hc.comp hv) measurable_const).inter
    (hreg.inter (measurableSet_lt (hc.comp ht) measurable_const)))))

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_CertificateUnion
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.FreeVisits

lemma largest_fiber {V : Type*} [Fintype V] {q : ℕ} (hq : 0<q) (f : V→Fin q) :
    ∃i : Fin q,Fintype.card V≤q*(Finset.univ.filter (fun v ↦ f v=i)).card := by
  classical
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hf : ∀v∈(Finset.univ : Finset V),f v∈(Finset.univ : Finset (Fin q)) := by simp
  have ht : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,hq⟩,Finset.mem_univ _⟩
  have hb : (Finset.univ : Finset (Fin q)).card • ((Fintype.card V:ℝ)/(q:ℝ))≤(Finset.univ : Finset V).card := by
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hq'.ne']
  obtain ⟨i,hi,h⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht hb
  refine ⟨i,?_⟩
  have hh := (div_le_iff₀ hq').mp h
  exact_mod_cast hh.trans_eq (mul_comm _ _)

lemma finite_failure_union {W V : Type*} [MeasurableSpace W] [Fintype V]
    (μ : Measure W) {q : ℕ} (hq : 0<q) (bad : Fin q→V→W→Prop)
    {p : ℝ≥0∞} (hp : p≤1)
    (hjoint : ∀i : Fin q,∀A : Finset V,μ {ω | ∀v∈A,bad i v ω}≤p^(q*A.card)) :
    μ {ω | ∀v,∃i,bad i v ω}≤((q:ℝ≥0∞)*p)^(Fintype.card V) := by
  classical
  have hsub : {ω | ∀v,∃i,bad i v ω}⊆⋃f : V→Fin q,{ω | ∀v,bad (f v) v ω} := by
    intro ω hω
    let f : V→Fin q := fun v ↦ Classical.choose (hω v)
    exact mem_iUnion.mpr ⟨f,fun v ↦ Classical.choose_spec (hω v)⟩
  have hf (f : V→Fin q) : μ {ω | ∀v,bad (f v) v ω}≤p^(Fintype.card V) := by
    obtain ⟨i,hi⟩ := largest_fiber hq f
    calc
      _ ≤ μ {ω | ∀v∈Finset.univ.filter (fun v ↦ f v=i),bad i v ω} := by
        apply measure_mono
        intro ω hω v hv
        rw [←(Finset.mem_filter.mp hv).2]
        exact hω v
      _ ≤ p^(q*(Finset.univ.filter (fun v ↦ f v=i)).card) := hjoint i _
      _ ≤ _ := pow_le_pow_right_of_le_one' hp hi
  calc
    _ ≤ μ (⋃f : V→Fin q,{ω | ∀v,bad (f v) v ω}) := measure_mono hsub
    _ ≤ ∑f : V→Fin q,μ {ω | ∀v,bad (f v) v ω} := measure_iUnion_fintype_le _ _
    _ ≤ ∑_f : V→Fin q,p^(Fintype.card V) := Finset.sum_le_sum (fun f _ ↦ hf f)
    _ = _ := by simp [nsmul_eq_mul,mul_pow]

end HardSphere.FreeVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateSix
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.FreeVisits
lemma finite_failure_union_finset {W V : Type*} [MeasurableSpace W] [DecidableEq V]
    (μ : Measure W) {q : ℕ} (hq : 0<q) (bad : Fin q→V→W→Prop)
    {p : ℝ≥0∞} (hp : p≤1)
    (hjoint : ∀i : Fin q,∀A : Finset V,μ {ω | ∀v∈A,bad i v ω}≤p^(q*A.card))
    (A : Finset V) :
    μ {ω | ∀v∈A,∃i,bad i v ω}≤((q:ℝ≥0∞)*p)^A.card := by
  let bad' (i : Fin q) (v : A) (ω : W) := bad i v ω
  have hj (i : Fin q) (B : Finset A) :
      μ {ω | ∀v∈B,bad' i v ω}≤p^(q*B.card) := by
    have h := hjoint i (B.image Subtype.val)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
    simpa only [Finset.mem_image,Set.ofPred_forall,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂] using h
  have h := finite_failure_union μ hq bad' hp hj
  convert h using 1
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq,Subtype.forall,bad']
  · simp only [Fintype.card_coe]
end HardSphere.FreeVisits
namespace HardSphere.Groups
open PathCutoff FreeVisits CellOrbital BathSlice Wiener HardSphere.Lattice

lemma not_certificate_iff {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) :
    ¬Certificate m r R C S s₀ ell θ H D u v ω ↔
      ∃i,certificateBad m r R C S s₀ ell θ H D u i v ω := by
  classical
  constructor
  · intro hn
    by_contra h
    have h0 := not_exists.mp h (0:Fin 6)
    have h1 := not_exists.mp h (1:Fin 6)
    have h2 := not_exists.mp h (2:Fin 6)
    have h3 := not_exists.mp h (3:Fin 6)
    have h4 := not_exists.mp h (4:Fin 6)
    have h5 := not_exists.mp h (5:Fin 6)
    simp [certificateBad] at h0 h1 h2 h3 h4 h5
    exact hn ⟨h0,h1,h2,h3,h4,h5⟩
  · rintro ⟨i,hi⟩ h
    fin_cases i
    · exact (not_lt.mpr h.low) hi
    · exact (not_le.mpr h.closeY) hi
    · exact (not_le.mpr h.closeZ) hi
    · exact (not_lt.mpr h.visit) hi
    · exact hi h.regular
    · exact (not_le.mpr h.long) hi

lemma certificate_joint {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time)
    (μ : Measure (ConfigurationPath N L)) {p : ℝ≥0∞} (hp : p≤1)
    (hjoint : ∀i : Fin 6,∀A : Finset (Fin 3→Fin K),
      μ {ω | ∀v∈A,certificateBad m r R C S s₀ ell θ H D u i v ω}≤p^(6*A.card))
    (A : Finset (Fin 3→Fin K)) :
    μ {ω | ∀v∈A,¬Certificate m r R C S s₀ ell θ H D u v ω}≤(6*p)^A.card := by
  simp only [not_certificate_iff]
  exact finite_failure_union_finset μ (by norm_num) _ hp hjoint A

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Mesh
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff

lemma sourceMesh_properties {t r : ℝ} (ht : 0<t) (hr : 0 < r) :
    0 < sourceMesh t r ∧ 0 < sourceStep t r ∧ sourceStep t r ≤ r^2 ∧
      (sourceMesh t r:ℝ)*sourceStep t r=2*t := by
  have hq : 0<t/r^2 := by positivity
  have hn : 0<⌈t/r^2⌉₊ := Nat.ceil_pos.mpr hq
  have hn' : 0<(⌈t/r^2⌉₊:ℝ) := by exact_mod_cast hn
  refine ⟨Nat.mul_pos (by norm_num) hn,by dsimp [sourceStep]; positivity,?_,?_⟩
  · change t/(⌈t/r^2⌉₊:ℝ) ≤ r^2
    apply (div_le_iff₀ hn').mpr
    have h := Nat.le_ceil (t/r^2)
    have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp h
    linarith
  · dsimp [sourceMesh,sourceStep]
    push_cast
    field_simp

lemma sourceMesh_bounds {t r D αmin αmax : ℝ}
    (ht : 0<t) (hr : 0 < r) (hD : 1≤D) (hαmin : 0<αmin)
    (hl : αmin≤D*r) (hu : D*r≤αmax) :
    (2*t/αmax^2)*D^2≤(sourceMesh t r:ℝ) ∧
    (sourceMesh t r:ℝ)≤(2*t/αmin^2+2)*D^2 := by
  have hDp : 0<D := by linarith
  have hαmax : 0<αmax := hαmin.trans_le (hl.trans hu)
  have hsq₁ : αmin^2≤D^2*r^2 := by nlinarith [sq_nonneg (D*r-αmin)]
  have hsq₂ : D^2*r^2≤αmax^2 := by nlinarith [sq_nonneg (αmax-D*r)]
  have hlo' : (t/αmax^2)*D^2≤t/r^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      _ = t*(D^2*r^2)/αmax^2 := by ring
      _ ≤ t*αmax^2/αmax^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq₂ ht.le) (sq_nonneg _)
      _ = t := by field_simp
  have hhi : t/r^2≤(t/αmin^2)*D^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    have hh : t*αmin^2≤t*(D^2*r^2) := mul_le_mul_of_nonneg_left hsq₁ ht.le
    have hh' := (le_div_iff₀ (sq_pos_of_pos hαmin)).mpr hh
    convert hh' using 1 <;> first | rfl | ring
  have hnlo := Nat.le_ceil (t/r^2)
  have hnhi := (Nat.ceil_lt_add_one (show 0≤t/r^2 by positivity)).le
  simp only [sourceMesh,Nat.cast_mul,Nat.cast_ofNat]
  have hDsq : 1≤D^2 := by nlinarith
  constructor
  · calc
      _ = 2*((t/αmax^2)*D^2) := by ring
      _ ≤ 2*(⌈t/r^2⌉₊:ℝ) := mul_le_mul_of_nonneg_left (hlo'.trans hnlo) (by norm_num)
  · calc
      _ ≤ 2*(t/r^2+1) := mul_le_mul_of_nonneg_left hnhi (by norm_num)
      _ ≤ 2*((t/αmin^2)*D^2+D^2) := by gcongr
      _ = _ := by ring
end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_EndpointTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma free_diameter_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {h S : ℝ} (hh : 0<h) (hS : 0≤S) (X : Configuration 1 L) :
    coordinateWiener 1 {w | S < intervalDiameter 0 1 (freeTrajectory 1 L h w X)} ≤
      3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2)) := by
  have hs : 0<Real.sqrt h := Real.sqrt_pos.mpr hh
  have hp := free_diameterRatio_tail htail hs (le_of_eq (Real.sq_sqrt hh.le).symm)
    (div_nonneg hS hs.le) X
  have he : {w | S < intervalDiameter 0 1 (freeTrajectory 1 L h w X)}=
      {w | S/Real.sqrt h < diameterRatio (Real.sqrt h) (freeTrajectory 1 L h w X)} := by
    ext w
    exact (div_lt_div_iff_of_pos_right hs).symm
  rw [he]
  convert hp using 2
  all_goals try with_reducible_and_instances rfl
  congr 3
  field_simp

lemma reversed_splitTime {s t : ℝ} (hs : 0 < s) (ht : 0<t) :
    reverseTime (splitTime s t hs ht)=splitTime t s ht hs := by
  apply Subtype.ext
  change 1-s/(s+t)=t/(t+s)
  have hh : s+t≠0 := by linarith
  field_simp; ring

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_RegularTail
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma free_endpoint_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {h t S : ℝ} (hh : 0 < h) (ht : 0<t) (hS : 0≤S) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬EndpointRegular (splitTime h t hh ht) S (freeTrajectory 1 L (h+t) w X)} ≤
      2*(3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2))) := by
  let p := 3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2))
  let E : Set (ConfigurationPath 1 L) := {ω | S < intervalDiameter 0 1 ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (intervalDiameter_continuous L 0 1).measurable
  have hp (Y : Configuration 1 L) : coordinateWiener 1 {w | freeTrajectory 1 L h w Y ∈ E} ≤ p :=
    free_diameter_tail htail hh hS Y
  have h₁ := free_prefix_event hh ht hE p hp X
  have h₂ := free_suffix_event ht hh hE p hp X
  have he : {w | ¬EndpointRegular (splitTime h t hh ht) S (freeTrajectory 1 L (h+t) w X)} =
      {w | configurationPrefix 1 L (splitTime h t hh ht) (freeTrajectory 1 L (h+t) w X) ∈ E} ∪
      {w | configurationSuffix 1 L (splitTime t h ht hh) (freeTrajectory 1 L (t+h) w X) ∈ E} := by
    ext w
    change (¬(intervalDiameter 0 (splitTime h t hh ht) _ ≤ S ∧ intervalDiameter (reverseTime (splitTime h t hh ht)) 1 _ ≤ S)) ↔
      (S < intervalDiameter 0 1 (configurationPrefix 1 L (splitTime h t hh ht) (freeTrajectory 1 L (h+t) w X)) ∨
       S < intervalDiameter 0 1 (configurationSuffix 1 L (splitTime t h ht hh) (freeTrajectory 1 L (t+h) w X)))
    rw [not_and_or,not_le,not_le,interval_prefix (splitTime h t hh ht),
      interval_suffix (reverseTime (splitTime h t hh ht)),reversed_splitTime,add_comm t h]
  rw [he]
  exact (measure_union_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

lemma free_regular_tail {c : ℝ} {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ R h S : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ ≤ r^2) (hR : 0≤R)
    (m : ℕ) (hm : 0 < m) (hh : 0 < h) (hhT : h < (m:ℝ)*τ) (hS : 0≤S) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬Regular m r R (meanCost+1)
      (splitTime h ((m:ℝ)*τ-h) hh (sub_pos.mpr hhT)) S (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(R/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+R)^3)))+
      2*(3*M*ENNReal.ofReal (Real.exp (-c*(S/(36*Real.sqrt h))^2))) := by
  have h₁ := free_mesh_regular_tail htail hr hτ hτr hR m hm X
  have h₂ := free_endpoint_regular_tail htail hh (sub_pos.mpr hhT) hS X
  rw [add_sub_cancel] at h₂
  have he : {w | ¬Regular m r R (meanCost+1) (splitTime h ((m:ℝ)*τ-h) hh (sub_pos.mpr hhT)) S (freeTrajectory 1 L ((m:ℝ)*τ) w X)} =
      {w | ¬MeshRegular m r R (meanCost+1) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ∪
      {w | ¬EndpointRegular (splitTime h ((m:ℝ)*τ-h) hh (sub_pos.mpr hhT)) S (freeTrajectory 1 L ((m:ℝ)*τ) w X)} := by
    ext w
    exact not_and_or
  rw [he]
  exact (measure_union_le _ _).trans (add_le_add h₁ h₂)

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_CutoffAsymptotics
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.PathCutoff

lemma stretched_exp_decay (p : ℝ) {b q : ℝ} (hb : 0<b) (hq : 0<q) :
    Tendsto (fun D:ℝ ↦ D^p*Real.exp (-b*D^q)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/q) b hb).comp
    (tendsto_rpow_atTop hq)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  dsimp
  rw [←Real.rpow_mul hD]
  congr 2
  field_simp

lemma scalarRegularBound_decay (p C M : ℝ) {c a b : ℝ}
    (hc : 0 < c) (ha : 0<a) (hb : 0<b) :
    Tendsto (fun D:ℝ ↦ D^p*scalarRegularBound C M c a b D) atTop (𝓝 0) := by
  have h₁ := (stretched_exp_decay (p+2) (by positivity : (0:ℝ) < c/1296)
    (by norm_num : (0:ℝ)<1/6)).const_mul (C*M)
  have h₂ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (a/8) (by positivity)
  have h₃ := (stretched_exp_decay p (by positivity : (0:ℝ) < c*b^2/82944)
    (by norm_num : (0:ℝ)<1/3)).const_mul (2*M)
  have ht := (h₁.add h₂).add h₃
  simp only [mul_zero,zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
  dsimp [scalarRegularBound]
  rw [Real.rpow_add hD,Real.rpow_two]
  ring

end HardSphere.PathCutoff

end

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace HardSphere.PathCutoff

lemma regularScale_mesh {D : ℝ} (hD : 0<D) :
    (D^(1/12:ℝ)/36)^2=D^(1/6:ℝ)/1296 := by
  rw [div_pow,←Real.rpow_natCast,←Real.rpow_mul hD.le]
  norm_num

lemma regularScale_endpoint {D b : ℝ} (hD : 0<D) :
    ((b*D^(-(1/3:ℝ))/8)/(36*Real.sqrt (D⁻¹)))^2=
      b^2/82944*D^(1/3:ℝ) := by
  rw [div_pow,mul_pow,div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤D⁻¹)]
  have hx : (D^(-(1/3:ℝ)))^2=D^(-(2/3:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num
  rw [hx]
  have he : D^(-(2/3:ℝ))*D=D^(1/3:ℝ) := by
    calc
      _ = D^(-(2/3:ℝ))*D^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hD]; norm_num
  calc
    _ = b^2/82944*(D^(-(2/3:ℝ))*D) := by field_simp; ring
    _ = _ := by rw [he]

lemma regularScale_denominator {D : ℝ} (hD : 1≤D) :
    (1+D^(1/12:ℝ))^3≤8*D := by
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hp : 1≤D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have hsum : 1+D^(1/12:ℝ)≤2*D^(1/12:ℝ) := by linarith
  have hp3 : (D^(1/12:ℝ))^3=D^(1/4:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD0.le]
    norm_num
  calc
    _ ≤ (2*D^(1/12:ℝ))^3 := pow_le_pow_left₀ (by positivity) hsum 3
    _ = 8*D^(1/4:ℝ) := by rw [mul_pow,hp3]; norm_num
    _ ≤ 8*D := by
      gcongr
      simpa using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (1/4:ℝ)≤1)

lemma regularScale_majorant {D C M c a b : ℝ} {m : ℕ}
    (hD : 1≤D) (_ : 0≤C) (hM : 0≤M) (_ : 0 ≤ c) (ha : 0≤a)
    (hmlo : a*D^2≤(m:ℝ)) (hmhi : (m:ℝ)≤C*D^2) :
    (m:ℝ)*(M*Real.exp (-c*(D^(1/12:ℝ)/36)^2))+
      Real.exp (-(m:ℝ)/((1+D^(1/12:ℝ))^3))+
      2*(M*Real.exp (-c*((b*D^(-(1/3:ℝ))/8)/(36*Real.sqrt (D⁻¹)))^2))≤
        scalarRegularBound C M c a b D := by
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hden : 0<(1+D^(1/12:ℝ))^3 := by positivity
  have hm : a/8*D≤(m:ℝ)/((1+D^(1/12:ℝ))^3) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (a/8*D)*(8*D) := mul_le_mul_of_nonneg_left (regularScale_denominator hD) (by positivity)
      _ = a*D^2 := by ring
      _ ≤ _ := hmlo
  rw [regularScale_mesh hD0,regularScale_endpoint hD0]
  unfold scalarRegularBound
  have hexp₁ : -c*(D^(1/6:ℝ)/1296)=-(c/1296)*D^(1/6:ℝ) := by ring
  have hexp₂ : -c*(b^2/82944*D^(1/3:ℝ))=-(c*b^2/82944)*D^(1/3:ℝ) := by ring
  rw [hexp₁,hexp₂]
  apply add_le_add _ (le_of_eq (by ring))
  apply add_le_add _ _
  · calc
      _ ≤ (C*D^2)*(M*Real.exp (-(c/1296)*D^(1/6:ℝ))) := mul_le_mul_of_nonneg_right hmhi (by positivity)
      _ = _ := by ring
  · apply Real.exp_le_exp.mpr
    rw [neg_div]
    nlinarith

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_StandardRegular
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace HardSphere.PathCutoff
open Wiener FreeVisits

lemma scalarRegularBound_nonneg {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (c a b D : ℝ) :
    0 ≤ scalarRegularBound C M c a b D := by unfold scalarRegularBound; positivity

lemma regular_root_decay {C M c a b : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun D:ℝ ↦ D*(scalarRegularBound C M c a b D)^(1/3:ℝ)) atTop (𝓝 0) := by
  have ht := (scalarRegularBound_decay (3:ℝ) C M hc ha hb).rpow_const (p:=(3⁻¹:ℝ)) (Or.inr (by positivity))
  rw [Real.zero_rpow (by norm_num : (3⁻¹:ℝ)≠0)] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  rw [Real.mul_rpow (Real.rpow_nonneg hD _) (scalarRegularBound_nonneg hC hM c a b D),
    ←Real.rpow_mul hD]
  norm_num

lemma free_regular_standard_tail {c : ℝ} {M : ℝ≥0∞} (hM : M≠⊤)
    (htail : ∀R:ℝ,0 ≤ R→wiener {w | R ≤ ‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ D C a b : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ ≤ r^2)
    (hc : 0 ≤ c) (hD : 1 ≤ D) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hm : 0 < m) (hmlo : a*D^2 ≤ (m:ℝ)) (hmhi : (m:ℝ) ≤ C*D^2)
    (hhT : D⁻¹ < (m:ℝ)*τ) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬Regular m r (D^(1/12:ℝ)) (meanCost+1)
      (splitTime (D⁻¹) ((m:ℝ)*τ-D⁻¹) (by positivity) (sub_pos.mpr hhT))
      (b*D^(-(1/3:ℝ))/8) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
        ENNReal.ofReal (scalarRegularBound C (3*M.toReal) c a b D) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hh := free_regular_tail htail hr hτ hτr (Real.rpow_nonneg hD0.le (1/12:ℝ)) m hm
    (by positivity : 0 < D⁻¹) hhT (by positivity : 0 ≤ b*D^(-(1/3:ℝ))/8) X
  apply hh.trans
  have hfinite : (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(D^(1/12:ℝ)/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+D^(1/12:ℝ))^3)))+
      2*(3*M*ENNReal.ofReal (Real.exp (-c*((b*D^(-(1/3:ℝ))/8)/(36*Real.sqrt (D⁻¹)))^2)))≠⊤ := by finiteness
  apply (ENNReal.le_ofReal_iff_toReal_le hfinite (scalarRegularBound_nonneg hC (by positivity) c a b D)).mpr
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact regularScale_majorant (M:=3*M.toReal) (b:=b) hD hC (by positivity) hc ha hmlo hmhi

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ShiftUniformMGF
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.ShiftVisits
open Wiener PathCutoff HardSphere.Lattice HardSphere.FreeVisits

theorem ground_regularVisitors_uniform :
    ∃ αstar : ℝ, 0 < αstar ∧ ∀ (η : ℝ), 0 < η → ∀ αmax C a b : ℝ,
      0 < αmax → 0 < C → 0 < a → 0 < b →
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → D₀ ≤ D → αstar ≤ D*r → D*r ≤ αmax → 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3 ≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (x₀ : Torus L) (A : Finset (DiscreteTorus K))
    (m : ℕ) (τ : ℝ) (_hm : 0 < m) (_hτ : 0 < τ), τ ≤ r^2 →
      a*D^2 ≤ (m:ℝ) → (m:ℝ) ≤ C*D^2 → (m:ℝ)*τ ≤ 2 →
    ∀ (hD : 0 < D) (hhT : D⁻¹ < (m:ℝ)*τ),
      groundPathLaw n L r ((m:ℝ)*τ) g {ω | ∀v∈A,1 ≤
        (visitorCount L x₀ {p | ¬Regular m r (D^(1/12:ℝ)) (meanCost+1)
          (splitTime D⁻¹ ((m:ℝ)*τ-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hhT))
          (b*D^(-(1/3:ℝ))/8) p} v ω:ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(η/2)*(A.card:ℝ))) := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  obtain ⟨Cd,Cs,α,hCd,hCs,hα,hmgf⟩ := interacting_visit_mgf_uniform
  refine ⟨α,hα,?_⟩
  intro η hη αmax C a b hαmax hC ha hb
  obtain ⟨Cf,hCf,hm⟩ := hmgf η hη.le
  let ε := fun D : ℝ ↦ scalarRegularBound C (3*M.toReal) c a b D
  let B := Real.exp (2*Cd*αmax)*Cf*η
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := min 1 (η/(2*Cs))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hlim : Tendsto (fun D : ℝ ↦ B*(D*(ε D)^(1/3:ℝ))) atTop (𝓝 0) := by
    simpa using (regular_root_decay hC.le (by positivity : 0 ≤ 3*M.toReal) hc ha hb).const_mul B
  obtain ⟨D₀,hsmall⟩ := (eventually_atTop.1
    ((eventually_ge_atTop (1:ℝ)).and (hlim.eventually (gt_mem_nhds hδ))))
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro n K inst L hL r D hDeq hDD hαr hαup hr hs g hg x₀ A m τ hmpos hτ hτr hmlo hmhi ht2 hD hhT
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hDD
  have hsmallD : B*(D*(ε D)^(1/3:ℝ)) ≤ δ := ((hsmall D ((le_max_right _ _).trans hDD)).2).le
  have hε : 0 ≤ ε D := scalarRegularBound_nonneg hC.le (by positivity) c a b D
  have ht : 0 < (m:ℝ)*τ := mul_pos (Nat.cast_pos.mpr hmpos) hτ
  have hxp : ((m:ℝ)*τ)*Cd*D*r ≤ 2*Cd*αmax := by
    calc
      _ = (((m:ℝ)*τ)*Cd)*(D*r) := by ring
      _ ≤ (((m:ℝ)*τ)*Cd)*αmax := mul_le_mul_of_nonneg_left hαup (by positivity)
      _ ≤ (2*Cd)*αmax := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hCd.le) hαmax.le
  let z := Real.exp (((m:ℝ)*τ)*Cd*D*r)*(Cf*η*(ε D)^(1/3:ℝ))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzD : z*D ≤ δ := by
    apply le_trans _ hsmallD
    calc
      _ ≤ Real.exp (2*Cd*αmax)*(Cf*η*(ε D)^(1/3:ℝ))*D := by
        dsimp [z]
        gcongr
      _ = B*(D*(ε D)^(1/3:ℝ)) := by dsimp [B]; ring
  have hz1 : z ≤ 1 := (by nlinarith : z ≤ z*D).trans (hzD.trans (min_le_left _ _))
  let E : Set (ConfigurationPath 1 L) := {p | ¬Regular m r (D^(1/12:ℝ)) (meanCost+1)
    (splitTime D⁻¹ ((m:ℝ)*τ-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hhT)) (b*D^(-(1/3:ℝ))/8) p}
  have hE : MeasurableSet E := (regular_measurable _ _ _ _ _ _).compl
  have hrev (p : ConfigurationPath 1 L) : reverseConfigurationPath 1 L p∈E ↔ p∈E :=
    (regular_reverse _ _ _ _ _ _ p).not
  have hp (y : Torus L) : coordinateWiener 1 {w | freeTrajectory 1 L ((m:ℝ)*τ) w (oneConfiguration y)∈E} ≤ ENNReal.ofReal (ε D) :=
    free_regular_standard_tail hM.ne htail hr hτ hτr hc.le hD1 hC.le ha.le hb.le m hmpos hmlo hmhi hhT (oneConfiguration y)
  have hh := hm n K L hL r D hDeq hD1 hαr hr hs g hg x₀ A ht ht2 hη.le (le_refl η) hε E hE hrev hp hz1
  have hj := joint_visitors_markov L x₀ A hE (groundPathLaw n L r ((m:ℝ)*τ) g) hη.le hh (H:=1)
  apply hj.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg A.card)
  have hδη : Cs*δ ≤ η/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < (2:ℝ)*Cs)).mp (min_le_right 1 (η/(2*Cs)))
    dsimp [δ]
    linarith
  have hcost := (mul_le_mul_of_nonneg_left hzD hCs.le).trans hδη
  change Cs*z*D-η*1 ≤ -(η/2)
  nlinarith

end HardSphere.ShiftVisits

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateSupply
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice

lemma exp_parameter {p : ℝ} (hp : 0<p) : ∃η : ℝ, 0<η ∧ Real.exp (-η/2)≤p^6 := by
  let η := 2*max 1 (-Real.log (p^6))
  have hη : 0<η := mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨η,hη,?_⟩
  calc
    _ ≤ Real.exp (Real.log (p^6)) := Real.exp_le_exp.mpr (by dsimp [η]; linarith [le_max_right 1 (-Real.log (p^6))])
    _ = _ := Real.exp_log (pow_pos hp 6)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SupplyIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance
attribute [local instance] Classical.propDecidable

lemma successExcept_measurable {L : Length} {N : ℕ} (n : ℕ) (r R C S : ℝ) (w : Time) (v : Point)
    (ω : Fin N → ConfigurationPath 1 L) (i : Fin N) :
    MeasurableSet (SuccessExcept n r R C S w v ω i) := by
  have h : MeasurableSet {f | ∀j,j≠i → ¬TrialCollision r (ω j) f} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ (trialCollision_closed r (ω j)).measurableSet.compl
  exact (trialCutoff_measurable L n r R C w S v).inter h

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateUseful
attribute [-instance] _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Sampling.siteAllocationKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma allocated_restriction_half_bad (E B : Finset I) (total q : ℕ)
    (hE : total≤E.card) (group : Fin (2*q)↪Fin total)
    (hB : 10*(E∩B).card≤E.card) :
    (allocationPMF E total).toMeasure
      {a | ∃f,a=some f ∧ q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^q) := by
  have hq : 2*q≤E.card := (show 2*q≤total by simpa using Fintype.card_le_of_embedding group).trans hE
  have h := allocation_half_bad E B q hq hB
  have hu := congrArg PMF.toMeasure (allocated_group_uniform E total (2*q) hE group)
  rw [←PMF.toMeasure_map _ _ (measurable_of_countable _)] at hu
  rw [←hu,Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete)] at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  ext a
  cases a with
  | none => simp
  | some f => simp

end HardSphere.Sampling

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CertificateWindow
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice

theorem ground_certificate_supply_ge_two :
    ∃ α₀ ell : ℝ, 2≤α₀ ∧ 0<ell ∧ ∀ θ : ℝ, 0<θ →
    ∃ b H t₀ : ℝ, 0<b ∧ b≤1/4 ∧ 0<H ∧ 0<t₀ ∧
    ∀ p : ℝ, 0<p → p≤1 → ∀ t : ℝ, 0<t → t≤t₀ →
    ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ D α : ℝ, 100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → α₀/2≤α → α≤2*α₀ →
    ∃ (hD : 0<D) (hh : D⁻¹<2*t), ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ A : Finset (Fin 3→Fin K),
      groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈A,
        ¬Certificate (sourceMesh t (α/D)) (α/D) (D^(1/12:ℝ)) (meanCost+1)
          (spatialCloseScale D b/8) (spatialCloseScale D b) ell θ H D
          (splitTime D⁻¹ (2*t-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hh)) v ω}≤
        (6*ENNReal.ofReal p)^A.card := by
  classical
  obtain ⟨αE,hαE,hex⟩ := ShiftVisits.ground_excessVisitors_tail
  obtain ⟨αL,hαL,hlong⟩ := ShiftVisits.ground_longVisitors_tail
  obtain ⟨αR,hαR,hreg⟩ := ShiftVisits.ground_regularVisitors_uniform
  let Amin := 2*max 1 (max αE (max αL αR))
  obtain ⟨α₀,ell,Dlow,Qlow,hA,hα₀,hell,hDlow,hQlow,hlow⟩ := grid_stationary_low_above Amin
  have htwo : 2≤α₀ := le_trans (by dsimp [Amin]; linarith [le_max_left (1:ℝ) (max αE (max αL αR))]) hA
  refine ⟨α₀,ell,htwo,hell,?_⟩
  intro θ hθ
  obtain ⟨Qc,hQc,hclose⟩ := grid_close_tail
  obtain ⟨b,Gc,hb,hb1,hGc,hclim,hclose⟩ := hclose θ hθ
  obtain ⟨Dc,hDc,hclose⟩ := hclose (2*α₀)
  obtain ⟨H,hH,hex⟩ := hex (2*α₀) (by positivity)
  obtain ⟨tL,htL,hlong⟩ := hlong (2*α₀) θ (by positivity) hθ
  let t₀ := min 1 (tL/2)
  have ht₀ : 0<t₀ := lt_min zero_lt_one (by positivity)
  refine ⟨b,H,t₀,hb,hb1,hH,ht₀,?_⟩
  intro p hp hp1 t ht htt
  have ht1 : t≤1 := htt.trans (min_le_left _ _)
  have htl : 2*t≤ min 2 tL := le_min (by linarith) (by have hh := htt.trans (min_le_right 1 (tL/2)); linarith)
  obtain ⟨η,hη,hηp⟩ := exp_parameter hp
  let C := 2*t/(α₀/2)^2+2
  let a := 2*t/(2*α₀)^2
  have hC : 0<C := by dsimp [C]; positivity
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨Dr,hDr,hreg⟩ := hreg η hη (2*α₀) C a b (by positivity) hC ha hb
  have hllim : Tendsto (fun D : ℝ ↦ Qlow/D^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0))
  have hexlim : Tendsto (fun D : ℝ ↦ Real.exp (-D)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hlonglim : Tendsto (fun D : ℝ ↦ Real.exp (-(θ*D/2))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : 0<θ/2))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext D
    simp only [Function.comp_apply,id_eq]
    congr 1
    ring
  have hinvlim : Tendsto (fun D : ℝ ↦ D⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero
  have hp6 : 0<p^6 := pow_pos hp _
  have hev : ∀ᶠ D : ℝ in atTop,
      1≤D ∧ Dlow≤D ∧ Dc≤D ∧ Dr≤D ∧ 2*(2*Real.pi*(2*α₀))^3≤D ∧
      Qlow/D^2≤p^6 ∧ (((Gc/b^2)*D^(-(4/3):ℝ))^(1/(Qc:ℝ)))≤p^6 ∧
      Real.exp (-D)≤p^6 ∧ Real.exp (-(θ*D/2))≤p^6 ∧ D⁻¹<2*t := by
    filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop Dlow,eventually_ge_atTop Dc,
      eventually_ge_atTop Dr,eventually_ge_atTop (2*(2*Real.pi*(2*α₀))^3),
      hllim.eventually (gt_mem_nhds hp6),hclim.eventually (gt_mem_nhds hp6),
      hexlim.eventually (gt_mem_nhds hp6),hlonglim.eventually (gt_mem_nhds hp6),
      hinvlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<2*t))] with D h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1,h2,h3,h4,h5,h6.le,h7.le,h8.le,h9.le,h10⟩
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.1 hev
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro n K inst instK L hLK D α hL hDeq hDD hαlo hαup
  obtain ⟨hD1,hDlow',hDc',hDr',hsmall',hlp,hcp,hep,hlgp,hinv⟩ := hD₀ D ((le_max_right _ _).trans hDD)
  have hD : 0<D := zero_lt_one.trans_le hD1
  have hα1 : 1≤α := by
    have hh := le_max_left 1 (max αE (max αL αR))
    dsimp [Amin] at hA
    linarith
  have hαe : αE≤α := by
    have hh := (le_max_left αE (max αL αR)).trans (le_max_right 1 (max αE (max αL αR)))
    dsimp [Amin] at hA
    linarith
  have hαl : αL≤α := by
    have hh := (le_max_left αL αR).trans ((le_max_right αE (max αL αR)).trans (le_max_right 1 (max αE (max αL αR))))
    dsimp [Amin] at hA
    linarith
  have hαr : αR≤α := by
    have hh := (le_max_right αL αR).trans ((le_max_right αE (max αL αR)).trans (le_max_right 1 (max αE (max αL αR))))
    dsimp [Amin] at hA
    linarith
  have hr : 0<α/D := div_pos (zero_lt_one.trans_le hα1) hD
  have hαeq : D*(α/D)=α := by field_simp
  have hsmall := smallness_of_large_density L hDeq hD1 (zero_le_one.trans hα1) hαup hsmall'
  have hK : 1≤K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  obtain ⟨hm,hτ,hτr,hspan⟩ := sourceMesh_properties ht hr
  obtain ⟨hmlo,hmhi⟩ := sourceMesh_bounds (αmax:=2*α₀) ht hr hD1 (by positivity : 0<α₀/2)
    (by rw [hαeq]; exact hαlo) (by rw [hαeq]; exact hαup)
  refine ⟨hD,hinv,?_⟩
  intro g hg A
  let u := splitTime D⁻¹ (2*t-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hinv)
  apply certificate_joint (sourceMesh t (α/D)) (α/D) (D^(1/12:ℝ)) (meanCost+1)
    (spatialCloseScale D b/8) (spatialCloseScale D b) ell θ H D u
    (groundPathLaw n L (α/D) (2*t) g) (ENNReal.ofReal_le_one.mpr hp1)
  intro i B
  fin_cases i
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,(centeredCount L (gridCenter L v) (ω 0):ℝ)<ell*D}≤_
    exact (hlow K n L D α hK hLK hDeq hDlow' hαlo hαup g hg (2*t) (by positivity) 0 B).trans
      (ofReal_power_tail (by positivity) hp.le hlp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω 0)).card:ℝ)}≤_
    exact (hclose n K L hLK D α hL hDeq hDc' hα1 hαup g hg (2*t) (by positivity) 0 B).trans
      (ofReal_power_tail (Real.rpow_nonneg (by positivity) _) hp.le hcp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω 1)).card:ℝ)}≤_
    exact (hclose n K L hLK D α hL hDeq hDc' hα1 hαup g hg (2*t) (by positivity) 1 B).trans
      (ofReal_power_tail (Real.rpow_nonneg (by positivity) _) hp.le hcp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,H*D<((visitors (gridCenter L v) ω).card:ℝ)}≤_
    have he := hex n K L hLK (α/D) D hDeq hD1 (by rwa [hαeq]) (by rwa [hαeq]) hr hsmall g hg
      (gridShift L) (B.image gridSite) (by positivity : 0<2*t) (by linarith : 2*t≤2)
    rw [Finset.card_image_of_injective _ gridSite_injective,←joint_event_image] at he
    simp only [grid_visitors_eq] at he
    apply (measure_mono (fun ω hω v hv ↦ (hω v hv).le)).trans
    exact he.trans (by simpa only [neg_mul] using exp_power_tail hp.le hep B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,¬∀j,pathVisitsBall L 12 (gridCenter L v) j ω→
      Regular (sourceMesh t (α/D)) (α/D) (D^(1/12:ℝ)) (meanCost+1) u (spatialCloseScale D b/8) (onePathAt j ω)}≤_
    have he := hreg n K L hLK (α/D) D hDeq hDr' (by rwa [hαeq]) (by rwa [hαeq]) hr hsmall g hg
      (gridShift L) (B.image gridSite) (sourceMesh t (α/D)) (sourceStep t (α/D)) hm hτ hτr
      hmlo hmhi (by rw [hspan]; linarith) hD (by rwa [hspan])
    rw [Finset.card_image_of_injective _ gridSite_injective,←joint_event_image] at he
    simp only [hspan,←grid_nonregular_iff] at he
    exact he.trans (by simpa only [neg_div] using exp_power_tail hp.le hηp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,θ*D≤((longVisitors (gridCenter L v) ω).card:ℝ)}≤_
    have he := hlong n K L hLK (α/D) D hDeq hD1 (by rwa [hαeq]) (by rwa [hαeq]) hr hsmall g hg
      (gridShift L) (B.image gridSite) (by positivity : 0<2*t) htl
    rw [Finset.card_image_of_injective _ gridSite_injective,←joint_event_image] at he
    simp only [grid_longVisitors_eq] at he
    exact he.trans (exp_power_tail hp.le hlgp B.card)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_GroupJoint
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
attribute [local instance] Classical.propDecidable

lemma certified_allocated_joint {W Z V : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    [Fintype V] [DecidableEq V] (μ : Measure W) [SFinite μ] (κ : Kernel W Z) [IsSFiniteKernel κ]
    (cert : V→W→Prop) (bad : V→W×Z→Prop)
    (hcert : ∀v,MeasurableSet {w | cert v w}) (hbad : ∀v,MeasurableSet {p | bad v p})
    (p q : ℝ≥0∞)
    (hjoint : ∀S : Finset V,μ {w | ∀v∈S,¬cert v w}≤p^S.card)
    (hcond : ∀w,∀T : Finset V,(∀v∈T,cert v w)→κ w {z | ∀v∈T,bad v (w,z)}≤q^T.card)
    (A : Finset V) :
    μ.compProd κ {wz | ∀v∈A,¬cert v wz.1 ∨ bad v wz}≤(p+q)^A.card := by
  let F : Finset V→Set (W×Z) := fun S ↦ {wz | (∀v∈S,¬cert v wz.1) ∧
    ∀v∈A\S,cert v wz.1 ∧ bad v wz}
  have hF (S : Finset V) : MeasurableSet (F S) := by
    have h₁ : MeasurableSet {p : W×Z | ∀v∈S,¬cert v p.1} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun v ↦ MeasurableSet.iInter (fun _ ↦ (hcert v).compl.preimage measurable_fst))
    have h₂ : MeasurableSet {p : W×Z | ∀v∈A\S,cert v p.1 ∧ bad v p} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun v ↦ MeasurableSet.iInter (fun _ ↦ ((hcert v).preimage measurable_fst).inter (hbad v)))
    exact h₁.inter h₂
  have hsub : {wz : W×Z | ∀v∈A,¬cert v wz.1 ∨ bad v wz}⊆⋃S∈A.powerset,F S := by
    intro wz hwz
    let S := A.filter (fun v ↦ ¬cert v wz.1)
    refine mem_iUnion.mpr ⟨S,mem_iUnion.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),?_⟩⟩
    constructor
    · exact fun v hv ↦ (Finset.mem_filter.mp hv).2
    · intro v hv
      obtain ⟨hvA,hvS⟩ := Finset.mem_sdiff.mp hv
      have hc : cert v wz.1 := by
        by_contra hn
        exact hvS (Finset.mem_filter.mpr ⟨hvA,hn⟩)
      exact ⟨hc,(hwz v hvA).resolve_left (not_not.mpr hc)⟩
  have hbound (S : Finset V) : μ.compProd κ (F S)≤p^S.card*q^(A\S).card := by
    rw [Measure.compProd_apply (hF S)]
    let C : Set W := {w | ∀v∈S,¬cert v w}
    have hC : MeasurableSet C := by
      simp only [C,ofPred_forall]
      exact MeasurableSet.iInter (fun v ↦ MeasurableSet.iInter (fun _ ↦ (hcert v).compl))
    calc
      _ ≤ ∫⁻w,C.indicator (fun _ ↦ q^(A\S).card) w ∂μ := by
        apply lintegral_mono
        intro w
        change κ w {z | (w,z)∈F S} ≤ _
        by_cases hc : w∈C
        · rw [Set.indicator_of_mem hc]
          by_cases hT : ∀v∈A\S,cert v w
          · apply (measure_mono (show {z | (w,z)∈F S}⊆{z | ∀v∈A\S,bad v (w,z)} from fun z hz v hv ↦ (hz.2 v hv).2)).trans
            exact hcond w (A\S) hT
          · have he : {z | (w,z)∈F S}=∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro z hz
              exact hT (fun v hv ↦ (hz.2 v hv).1)
            rw [he,measure_empty]
            exact bot_le
        · rw [Set.indicator_of_notMem hc]
          have he : {z | (w,z)∈F S}=∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            exact hc hz.1
          rw [he,measure_empty]
      _ = q^(A\S).card*μ C := by rw [lintegral_indicator hC]; simp
      _ ≤ q^(A\S).card*p^S.card := mul_le_mul_right (hjoint S) _
      _ = _ := mul_comm _ _
  calc
    _ ≤ μ.compProd κ (⋃S∈A.powerset,F S) := measure_mono hsub
    _ ≤ ∑S∈A.powerset,μ.compProd κ (F S) := measure_biUnion_finset_le _ _
    _ ≤ ∑S∈A.powerset,p^S.card*q^(A\S).card := Finset.sum_le_sum (fun S _ ↦ hbound S)
    _ = _ := by
      calc
        _ = ∑S∈A.powerset,p^S.card*q^(A.card-S.card) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hS)]
        _ = _ := Finset.sum_pow_mul_eq_add_pow p q A

end HardSphere.Groups

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SiteGroups
attribute [-instance] _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
lemma siteAllocation_joint_half_bad (E B : V→Finset I) (total q : ℕ)
    (group : Fin (2*q)↪Fin total) (T : Finset V)
    (hE : ∀v∈T,total ≤ (E v).card)
    (hB : ∀v∈T,10*(E v∩B v).card ≤ (E v).card) :
    siteAllocationKernel total E
      {a | ∀v∈T,∃f,a v=some f ∧ q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B v)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^q)^T.card := by
  change Measure.pi (fun v ↦ (allocationPMF (E v) total).toMeasure) _ ≤ _
  have he : {a : V→Allocation total I | ∀v∈T,∃f,a v=some f ∧
      q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B v)).card}=
      (↑T : Set V).pi (fun v ↦ {a | ∃f,a=some f ∧
        q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B v)).card}) := by
    rfl
  rw [he,Measure.pi_pi_finset]
  calc
    _ ≤ ∏v∈T,ENNReal.ofReal ((2/5:ℝ)^q) :=
      Finset.prod_le_prod' (fun v hv ↦ allocated_restriction_half_bad
        (E v) (B v) total q (hE v hv) group (hB v hv))
    _ = _ := by simp

end HardSphere.Sampling

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDatum
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalDatum_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) :
    Measurable (physicalDatum (N:=N) (K:=K) (M:=M) (L:=L) g m r R C S s₀ u) := by
  unfold physicalDatum
  apply ((continuous_eval_const 0).measurable.comp measurable_fst).prodMk
  apply ((continuous_eval_const 1).measurable.comp measurable_fst).prodMk
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    have h : MeasurableSet {z : ConfigurationPath N L × GridAllocation N K (G*M) |
        ∃v : Fin 3 → Fin K, Eligible m r R C S s₀ u v i z.1} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun v ↦
        (eligible_measurable m r R C S s₀ u v i).preimage measurable_fst
    apply measurable_to_countable'
    intro b
    cases b
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_false_iff_not,←Set.compl_ofPred] using h.compl
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq] using h
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  apply Measurable.ite
    (measurable_snd ((Set.to_countable {a : GridAllocation N K (G*M) | i∈groupUnion g a}).measurableSet))
    measurable_const
  exact (onePathAt_continuous i).measurable.comp measurable_fst

attribute [local irreducible] TrialCollision

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTargets
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma datumBad_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) :
    Measurable (datumBad (N:=N) (M:=M) hL g m t r R C S u) := by
  apply measurable_to_countable'
  intro f
  change MeasurableSet {d | _ = f}
  have he : {d : PhysicalDatum N K M G L | datumBad hL g m t r R C S u d=f} =
    ⋂v : Fin 3 → Fin K, {d | (2*(datumAccessibleLabels hL g m t r R C S u v d).card<M) ↔ v∈f} := by
    ext d
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    rw [Finset.ext_iff]
    simp only [datumBad,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he]
  apply MeasurableSet.iInter
  intro v
  have hh := (datumAccessibleLabels_measurable (M:=M) hL g m t r R C S u v)
    ((Set.to_countable {s : Finset (Fin N) | 2*s.card<M}).measurableSet)
  by_cases hv : v∈f
  · simpa only [hv,iff_true,Set.preimage_ofPred_eq] using hh
  · simpa only [hv,iff_false,Set.preimage_ofPred_eq,←Set.compl_ofPred] using hh.compl

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_TaggedReference
attribute [-instance] _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq I] [DecidableEq V] in
lemma siteAllocation_supported (E : V→Finset I) (total : ℕ) :
    siteAllocationKernel total E {a | ∀v,a v∈(allocationPMF (E v) total).support}=1 := by
  change Measure.pi (fun v ↦ (allocationPMF (E v) total).toMeasure) _=1
  have he : {a : V→Allocation total I | ∀v,a v∈(allocationPMF (E v) total).support}=
      Set.univ.pi (fun v ↦ (allocationPMF (E v) total).support) := by ext a; simp
  rw [he,Measure.pi_pi]
  apply Finset.prod_eq_one
  intro v _
  exact (PMF.toMeasure_apply_eq_one_iff _ (MeasurableSet.of_discrete)).mpr (Subset.refl _)

end HardSphere.Sampling

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupply
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalDatum_home {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (v : Fin 3 → Fin K) (i : Fin N) (hi : Eligible m r R C S s₀ u v i ω) :
    datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v :=
  (gridHome_eq_iff hL hK (ω 0 i) v).mpr hi.1.1

lemma full_success_datum {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (n : ℕ) (t r R C S s₀ : ℝ) (w : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (v : Fin 3 → Fin K) (i : Fin N)
    (hi : Eligible (n+n) r R C S s₀ (prefixTime midpointTime w) v i ω)
    (his : i∈groupUnion g a)
    (hs : StrongExcept n t r R C S w
      (nearestLift L (anchorPoint v) (ω 0 i)) (nearestLift L (anchorPoint v) (ω 1 i))
      (anchorPoint v) (fun j ↦ onePathAt j ω) i (fun j ↦ unitTarget (anchorPoint v+targetStep j))) :
    datumAccessible hL g (n+n) t r R C S (prefixTime midpointTime w) i
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a)) := by
  let d := physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a)
  have hh : datumHome hL d i=v := physicalDatum_home hL hK g _ _ _ _ _ _ _ ω a v i hi
  have hy : datumStart hL d i=nearestLift L (anchorPoint v) (ω 0 i) := by
    unfold datumStart
    rw [hh]
    rfl
  have hz : datumEnd hL d i=nearestLift L (anchorPoint v) (ω 1 i) := by
    unfold datumEnd
    rw [hh]
    rfl
  change ∀j : Fin 7, _ ≤ volume (Prod.mk d ⁻¹' datumTarget hL g (n+n) t r R C S (prefixTime midpointTime w) i j)
  intro j
  have hsj := hs j
  rw [Measure.restrict_apply₀] at hsj
  · refine hsj.trans (measure_mono ?_)
    intro U hU
    refine ⟨?_,?_⟩
    · change U∈unitTarget (anchorPoint (datumHome hL d i)+targetStep j)
      simpa only [hh] using hU.2
    · change ENNReal.ofReal (9/10:ℝ)≤datumSuccess hL g (n+n) t r R C S (prefixTime midpointTime w) i (d,U)
      refine hU.1.trans ?_
      unfold datumSuccess
      rw [hy,hz]
      rw [←trialKernel_pin]
      apply measure_mono
      intro f hf
      change Regular (n+n) r R C (prefixTime midpointTime w) S (projectCurve L f) ∧
        TrialConfined L (anchorPoint (datumHome hL d i)) f ∧
        f∈fixedEndpoints (datumStart hL d i) (datumEnd hL d i) ∧ _
      rw [hh,hy,hz]
      refine ⟨hf.1.1.1,hf.1.1.2,hf.2,?_⟩
      intro k hk
      have hk' : k∉groupUnion g a := hk
      have hki : k≠i := by intro he; exact hk' (he ▸ his)
      simpa only [d,physicalDatum,ite_eq_right hk'] using hf.1.2 k hki
  · exact (measurableSet_le measurable_const ((trialKernel t _ _).measurable_coe
      (successExcept_measurable n r R C S w (anchorPoint v) (fun j ↦ onePathAt j ω) i))).nullMeasurableSet

lemma allocation_some_of_supported {I : Type*} [Fintype I] [DecidableEq I]
    (E : Finset I) (total : ℕ) (hE : total≤E.card) (a : Allocation total I)
    (ha : a∈(allocationPMF E total).support) : ∃f,a=some f := by
  have : Nonempty (Fin total↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hE)
  rw [allocationPMF_large E total hE,PMF.support_map] at ha
  obtain ⟨f,_,rfl⟩ := ha
  exact ⟨_,rfl⟩

lemma datumBad_forces_half_failure {N K G q : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (g : Fin G)
    (n : ℕ) (t r R C S s₀ : ℝ) (w : Time) (v : Fin 3 → Fin K)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*(2*q)))
    (ha : a v∈(allocationPMF (eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω) (G*(2*q))).support)
    (hE : G*(2*q)≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card)
    (hb : v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a))) :
    ∃f,a v=some f ∧ q≤(Finset.univ.filter fun k ↦
      f (groupPosition (2*q) G g k)∈fullFailure n t r R C S w v ω).card := by
  obtain ⟨f,hf⟩ := allocation_some_of_supported _ _ hE (a v) ha
  refine ⟨f,hf,?_⟩
  let d := physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a)
  let P : Fin (2*q) → Prop := fun k ↦ f (groupPosition (2*q) G g k)∈fullFailure n t r R C S w v ω
  let good := Finset.univ.filter fun k ↦ ¬P k
  have hinj : Function.Injective (fun k ↦ f (groupPosition (2*q) G g k)) :=
    f.injective.comp (groupPosition (2*q) G g).injective
  have hsub : good.image (fun k ↦ f (groupPosition (2*q) G g k))⊆
      datumAccessibleLabels hL g (n+n) t r R C S (prefixTime midpointTime w) v d := by
    intro i hi
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    have hiE := allocationPMF_support _ _ _ ha f hf (groupPosition (2*q) G g k)
    have hel := (Finset.mem_filter.mp hiE).2
    have hsel : f (groupPosition (2*q) G g k)∈groupUnion g a :=
      Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ v,by simp [groupAt,hf]⟩
    have hstrong : StrongExcept n t r R C S w
        (nearestLift L (anchorPoint v) (ω 0 (f (groupPosition (2*q) G g k))))
        (nearestLift L (anchorPoint v) (ω 1 (f (groupPosition (2*q) G g k))))
        (anchorPoint v) (fun j ↦ onePathAt j ω) (f (groupPosition (2*q) G g k))
        (fun j ↦ unitTarget (anchorPoint v+targetStep j)) := by
      have hh := (Finset.mem_filter.mp hk).2
      simpa only [P,fullFailure,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hh
    exact Finset.mem_filter.mpr ⟨hsel,physicalDatum_home hL hK g _ _ _ _ _ _ _ ω a v _ hel,
      full_success_datum hL hK g n t r R C S s₀ w ω a v _ hel hsel hstrong⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hbad := (Finset.mem_filter.mp hb).2
  have hc := Finset.card_filter_add_card_filter_not (s:=Finset.univ) P
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  change (Finset.univ.filter P).card+good.card=2*q at hc
  change q≤(Finset.univ.filter P).card
  change 2*(datumAccessibleLabels hL g (n+n) t r R C S (prefixTime midpointTime w) v d).card<2*q at hbad
  omega

theorem physicalDatum_joint_half_failure {N K G q : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (g : Fin G)
    (n : ℕ) (t r R C S s₀ : ℝ) (w : Time) (ω : ConfigurationPath N L)
    (T : Finset (Fin 3 → Fin K))
    (hE : ∀v∈T,G*(2*q)≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card)
    (hB : ∀v∈T,10*((eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω)∩
      fullFailure n t r R C S w v ω).card≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card) :
    physicalAllocationKernel (n+n) (G*(2*q)) r R C S s₀ (prefixTime midpointTime w) ω
      {a | ∀v∈T,v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
        (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a))}≤
      ENNReal.ofReal ((2/5:ℝ)^q)^T.card := by
  let E := fun v : Fin 3 → Fin K ↦ eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω
  change siteAllocationKernel (G*(2*q)) E _≤_
  have hs : ∀ᵐa ∂siteAllocationKernel (G*(2*q)) E,
      ∀v,a v∈(allocationPMF (E v) (G*(2*q))).support := by
    rw [ae_iff_measure_eq (MeasurableSet.of_discrete : MeasurableSet {a : GridAllocation N K (G*(2*q)) | ∀v,a v∈(allocationPMF (E v) (G*(2*q))).support}).nullMeasurableSet]
    simpa only [measure_univ] using siteAllocation_supported E (G*(2*q))
  refine (measure_mono_ae ?_).trans
    (siteAllocation_joint_half_bad E (fun v ↦ fullFailure n t r R C S w v ω)
      (G*(2*q)) q (groupPosition (2*q) G g) T hE hB)
  filter_upwards [hs] with a ha
  intro hb v hv
  exact datumBad_forces_half_failure hL hK g n t r R C S s₀ w v ω a (ha v) (hE v hv) (hb v hv)

lemma physical_bad_joint_of_certified_counts {N K G q : ℕ} [NeZero K]
    [Nontrivial (Fin N)] {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (n : ℕ) (t r R C S s₀ ell θ H D : ℝ) (w : Time)
    (μ : Measure (ConfigurationPath N L)) [SFinite μ] (p : ℝ≥0∞)
    (hjoint : ∀A : Finset (Fin 3→Fin K),μ {ω | ∀v∈A,
      ¬Certificate (n+n) r R C S s₀ ell θ H D (prefixTime midpointTime w) v ω}≤p^A.card)
    (hcount : ∀v : Fin 3→Fin K,∀ω : ConfigurationPath N L,
      Certificate (n+n) r R C S s₀ ell θ H D (prefixTime midpointTime w) v ω →
      G*(2*q)≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card ∧
      10*((eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω)∩
        fullFailure n t r R C S w v ω).card≤
        (eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card)
    (A : Finset (Fin 3→Fin K)) :
    ((μ.compProd (physicalAllocationKernel (n+n) (G*(2*q)) r R C S s₀ (prefixTime midpointTime w))).map
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w)))
      {d | A⊆datumBad hL g (n+n) t r R C S (prefixTime midpointTime w) d}≤
      (p+ENNReal.ofReal ((2/5:ℝ)^q))^A.card := by
  have hK : 1≤K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hbad (v : Fin 3→Fin K) : MeasurableSet {z : ConfigurationPath N L×GridAllocation N K (G*(2*q)) |
      v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
        (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) z)} :=
    ((datumBad_measurable (M:=2*q) hL g (n+n) t r R C S (prefixTime midpointTime w)).comp
      (physicalDatum_measurable g (n+n) r R C S s₀ (prefixTime midpointTime w)))
      ((Set.to_countable {B : Finset (Fin 3→Fin K) | v∈B}).measurableSet)
  have hEvent : MeasurableSet {d : PhysicalDatum N K (2*q) G L |
      A⊆datumBad hL g (n+n) t r R C S (prefixTime midpointTime w) d} :=
    (datumBad_measurable hL g (n+n) t r R C S (prefixTime midpointTime w))
      ((Set.to_countable {B : Finset (Fin 3→Fin K) | A⊆B}).measurableSet)
  rw [Measure.map_apply (physicalDatum_measurable g (n+n) r R C S s₀ (prefixTime midpointTime w)) hEvent]
  have H := certified_allocated_joint μ (physicalAllocationKernel (K:=K) (n+n) (G*(2*q)) r R C S s₀ (prefixTime midpointTime w))
    (fun v ω ↦ Certificate (n+n) r R C S s₀ ell θ H D (prefixTime midpointTime w) v ω)
    (fun v z ↦ v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) z))
    (fun v ↦ certificate_measurable _ _ _ _ _ _ _ _ _ _ _ v) hbad p
    (ENNReal.ofReal ((2/5:ℝ)^q)) hjoint
    (fun ω T hc ↦ physicalDatum_joint_half_failure hL hK g n t r R C S s₀ w ω T
      (fun v hv ↦ (hcount v ω (hc v hv)).1) (fun v hv ↦ (hcount v ω (hc v hv)).2)) A
  refine (measure_mono ?_).trans H
  intro z hz v hv
  exact Or.inr (hz hv)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalGroundSupply
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma source_boundary_eq {D t : ℝ} (hD : 0<D) (ht : 0<t) (hh : D⁻¹<2*t)
    (w : Time) (hw : t*(w:ℝ)=D⁻¹) :
    prefixTime midpointTime w=splitTime D⁻¹ (2*t-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hh) := by
  apply Subtype.ext
  change (1/2:ℝ)*(w:ℝ)=D⁻¹/(D⁻¹+(2*t-D⁻¹))
  rw [show D⁻¹+(2*t-D⁻¹)=2*t by ring]
  apply (eq_div_iff (by positivity : (2*t)≠0)).mpr
  nlinarith

theorem physical_ground_bad_supply_oai :
    ∃A ell b H t₀ : ℝ,2≤A ∧ 0<ell ∧ 0<b ∧ 0<H ∧ 0<t₀ ∧
    ∀t : ℝ,0<t → t≤t₀ → ∀p : ℝ,0<p → p≤1 →
    ∃D₀ : ℝ,1≤D₀ ∧ ∀{N K q G : ℕ} [Nontrivial (Fin N)] [NeZero K] {L : Length},
    ∀hL : L.val=(K:ℝ),100≤L.val → ∀D α : ℝ,D=(N:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀w : Time,t*(w:ℝ)=D⁻¹ → (G*(2*q):ℝ)≤ell*D/2 →
    ∀ψ : Jet N L,IsGroundVector N L (α/D) ψ → ∀g : Fin G,∀T : Finset (Fin 3→Fin K),
      physicalDatumLaw g ψ (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ))
        (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (2*t) (prefixTime midpointTime w)
        {d : PhysicalDatum N K (2*q) G L | T⊆datumBad hL g (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊)
          t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (prefixTime midpointTime w) d}≤
        (6*ENNReal.ofReal p+ENNReal.ofReal ((2/5:ℝ)^q))^T.card := by
  obtain ⟨A,ell,hA2,hell,hcert⟩ := ground_certificate_supply_ge_two
  have hA : 0<A := by linarith
  obtain ⟨b,H,tc,hb,hb4,hH,htc,hcert⟩ := hcert (ell/12) (by positivity)
  obtain ⟨ts,hts,hsupply⟩ := canonical_supply_counts hell hb (by positivity : 0<A/2) (by positivity : 0<2*A) hH
  refine ⟨A,ell,b,H,min tc ts,hA2,hell,hb,hH,lt_min htc hts,?_⟩
  intro t ht htt p hp hp1
  obtain ⟨Dc,hDc,hcert⟩ := hcert p hp hp1 t ht (htt.trans (min_le_left _ _))
  obtain ⟨Ds,hDs,hsupply⟩ := hsupply t ht (htt.trans (min_le_right _ _))
  refine ⟨max Dc Ds,hDc.trans (le_max_left _ _),?_⟩
  intro N K q G instN instK L hL h100 D α hDeq hD hαlo hαhi w hw hG ψ hψ g T
  have hDDc := (le_max_left Dc Ds).trans hD
  have hDDs := (le_max_right Dc Ds).trans hD
  obtain ⟨hDp,hh,hcert⟩ := hcert N K L hL D α h100 hDeq hDDc hαlo hαhi
  have hwindow := source_boundary_eq hDp ht hh w hw
  let C := 64*(meanCost+1)
  have hC : meanCost+1≤C := by dsimp [C]; nlinarith [meanCost_nonneg]
  have hjoint : ∀T : Finset (Fin 3→Fin K),
      groundPathLaw N L (α/D) (2*t) ψ {ω | ∀v∈T,¬Certificate
        (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D (prefixTime midpointTime w) v ω}≤
      (6*ENNReal.ofReal p)^T.card := by
    intro T
    refine (measure_mono ?_).trans (hcert ψ hψ T)
    intro ω hω v hv hc
    apply hω v hv
    have hc' := certificate_mono_constants le_rfl hC hc
    rw [←hwindow] at hc'
    simpa only [sourceMesh,two_mul,spatialCloseScale] using hc'
  have hcounts (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
      (hc : Certificate (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D (prefixTime midpointTime w) v ω) :=
    hsupply D α hDDs hαlo hαhi N K ⌈t/(α/D)^2⌉₊ L (by linarith) rfl w hw (ell/12) (by linarith) v ω hc
  have hcfull (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
      (hc : Certificate (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D (prefixTime midpointTime w) v ω) :
      G*(2*q)≤(eligibleList (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω).card ∧
      10*((eligibleList (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω)∩
        fullFailure ⌈t/(α/D)^2⌉₊ t (α/D) (D^(1/12:ℝ)) C (b*D^(-(1/3):ℝ)/8) w v ω).card≤
        (eligibleList (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ)) C
        (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω).card := by
    obtain ⟨hlo,hbad⟩ := hcounts v ω hc
    refine ⟨?_,hbad⟩
    exact_mod_cast hG.trans hlo
  let := hψ.groundPathLaw_probability (by linarith : 0≤2*t)
  exact physical_bad_joint_of_certified_counts hL g ⌈t/(α/D)^2⌉₊ t (α/D) (D^(1/12:ℝ)) C
    (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell (ell/12) H D w
    (groundPathLaw N L (α/D) (2*t) ψ) (6*ENNReal.ofReal p) hjoint hcfull T

end HardSphere.Groups
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.Groups.physical_ground_bad_supply_oai := @OAI.HardSphere.Groups.physical_ground_bad_supply_oai
