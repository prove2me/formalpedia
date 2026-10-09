-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.original_input_local_blocks_subpower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:38:50.524446+00:00
-- url     : https://prove2.me/submissions/5072c435-c74b-4452-a159-a4c4e6bf1ed9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace ActualEisensteinCubic

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

open ConcreteTraceCRT

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CompleteCommon
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem commonPart_ne_zero (I J : Ideal O) : commonPart I J ≠ 0 := by
  rw [commonPart_eq_supportExtract]
  exact supportExtract_ne_zero _ _

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DyadicCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

lemma retained_integral_mem (R q : ℝ) (hq : 1≤q) (n : ℤ)
    (hr : Retained R n) (hne : dyadicWeight n q≠0) :
    n∈indices 1 (max 1 R) := by
  rw [mem_indices_iff_scale 1 (max 1 R) (by norm_num) (by positivity) n]
  exact ⟨hq.trans (dyadicWeight_support n hne).2.le,
    (retained_scale_le R n hr).trans (by linarith [le_max_right (1:ℝ) R])⟩

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤C) (hR : 0≤R)
    (hZ : 1≤Z) (ha : 0<a) (hab : a≤b) (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=>ActualEisensteinCubic.O

lemma mem_retainedIndices (R:ℝ)(n:ℤ):
    n∈retainedIndices R↔Retained R n ∧ ∃q:ℝ,1≤q ∧ dyadicWeight n q≠0 :=
  (finite_retained_integral_dyads R).mem_toFinset

lemma effectiveScale_pos (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ)(hK:0<K):
    0<effectiveScale C D E K:=by
  unfold effectiveScale
  apply div_pos (div_pos hK ?_) ?_
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _)))

end SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentDyadicCount

lemma indices_mono_upper (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hbc : b≤ c) :
    indices a b ⊆ indices a c := by
  intro n hn
  rw [mem_indices_iff_scale a c ha (hb.trans_le hbc)]
  have h := (mem_indices_iff_scale a b ha hb n).mp hn
  exact ⟨h.1,h.2.trans (by linarith)⟩

lemma blocks_card_le (K R H nC nD : ℝ) (hH : 0<H)
    (hC : 1≤nC) (hD : 1≤nD) :
    Fintype.card (Blocks K R (H/nC) (H/nD)) ≤
      Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
        (![K,max 1 R,max 1 H,max 1 H] i))) := by
  have hcol (n : ℝ) (hn : 1≤n) : indices 1 (H/n) ⊆ indices 1 (max 1 H) := by
    apply indices_mono_upper _ _ _ (by norm_num) (div_pos hH (zero_lt_one.trans_le hn))
    exact (div_le_self hH.le hn).trans (le_max_right _ _)
  have hs (i : Fin 4) : bands K R (H/nC) (H/nD) i ⊆
      indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i) := by
    fin_cases i
    · exact Finset.Subset.refl _
    · intro n hn
      obtain ⟨hr,q,hq,hne⟩ := (mem_retainedIndices R n).mp hn
      exact retained_integral_mem R q hq n hr hne
    · exact hcol nC hC
    · exact hcol nD hD
  let f : Blocks K R (H/nC) (H/nD) →
      (∀i:Fin 4,↥(indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i))) :=
    fun x i => ⟨x i,hs i (x i).property⟩
  apply Fintype.card_le_of_injective f
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrArg (fun z => (z i).val) hxy

set_option maxHeartbeats 1000000 in
theorem blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀K R H nC nD : ℝ,0<K → 0<H → 1≤nC → 1≤nD →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 Cr) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro K R H nC nD hK hH hnC hnD hR hHcap
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hbound : 1≤ max 1 Cr*Z^(B+L) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hp
  have hR' : max 1 R≤ max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hR.trans (mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (Real.rpow_nonneg hz.le _) (by positivity))
  have hH' : max 1 H≤ max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hHcap.trans ((Real.rpow_le_rpow_of_exponent_le hZ (by linarith : B≤B+L)).trans
      (le_mul_of_one_le_left (zero_le_one.trans hp) (le_max_left _ _)))
  have hfour := hcount ![K,1,1,1] ![K,max 1 R,max 1 H,max 1 H]
    (by intro i;fin_cases i <;> simp_all)
    (by intro i;fin_cases i <;> simp)
    (by intro i;fin_cases i
        · simpa [div_self hK.ne'] using hbound
        · simpa using hR'
        · simpa using hH'
        · simpa using hH')
  exact (show (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤
    Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
      (![K,max 1 R,max 1 H,max 1 H] i))) by
      exact_mod_cast blocks_card_le K R H nC nD hH hnC hnD).trans hfour

theorem original_blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D : Ideal ActualEisensteinCubic.O), C≠0 → D≠0 →
      ∀(E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
        (K R H : ℝ),0<K → 0<H → R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks (effectiveScale C D E K) R
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := blocks_subpower B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro C D hC hD E K R H hK hH hR hHcap
  have norm_one (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
      (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hcount _ _ _ _ _ (effectiveScale_pos C D E K hK) hH
    (norm_one C hC) (norm_one D hD) hR hHcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_frequency_radius_cap (I J:Ideal O)(E:Finset (CommonIndex I J))
    (K V Z B ξ:ℝ)(hK:0<K)(hV:0≤V)(hZ:1≤Z)
    (hVcap:V≤Z^B)(hKcap:K⁻¹≤Z^B):
    frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K V) Z ξ≤Z^(3*B+ξ/2) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hT:V^2/K≤Z^(3*B):=by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV hVcap 2) hKcap
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  unfold frequencyRadius
  calc
    _≤Z^(3*B)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      ((first_nominal_scale_le I J E K V hK).trans hT) (Real.rpow_nonneg hz.le _)
    _=_:=by rw [←Real.rpow_add hz]

theorem original_local_blocks_subpower (B Hcap ξ ε:ℝ)
    (hB:0≤B)(hHcap:0≤Hcap)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K V H:ℝ),
      0<K→0≤V→0<H→V≤Z^B→K⁻¹≤Z^B→H≤Z^Hcap→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K V) Z ξ)
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_blocks_subpower Hcap (3*B+ξ/2) 1 ε
    hHcap (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro C D hC hD E K V H hK hV hH hVcap hKcap hHbound
  exact hcount C D hC hD E K _ H hK hH
    (by simpa only [one_mul] using (local_frequency_radius_cap C D E K V Z B ξ
      hK hV hZ hVcap hKcap)) hHbound

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤hi i)(hb₁:|s.b₁|≤b₁)(hb₂:|s.b₂|≤b₂)
    (hZ:1≤Z)(hfixed:(∏i,hi i)*b₁*b₂≤Z)
    (hV:volume s.toData≤Z^B):sourceRadius s≤Z^(B+1) := by
  have hVol:0<volume s.toData:=volume_pos s.toData
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s.toData:=by
    unfold sourceRadius volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>hhi i)
  have hb₁0:0≤b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

theorem original_input_local_blocks_subpower_oai {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (volume s.toData)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_local_blocks_subpower B (B+1) ξ ε
    hB (by positivity) hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hcount hZ hfixed
  intro s hhi hb₁ hb₂ hH C D hC hD E K hK hV hKi
  exact hcount C D hC hD E K _ _ hK (volume_pos s.toData).le hH hV hKi
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.original_input_local_blocks_subpower_oai.{u_1} := @OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.original_input_local_blocks_subpower_oai.{u_1}
