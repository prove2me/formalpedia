-- Prove2me | solution 1 for LogLogJam.Supplement.fixed_count_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:26:59.704815+00:00
-- url     : https://prove2.me/submissions/21c1f06c-9087-4b0c-8d39-17f7f27f7ba7

import Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
import Theorems.Thm_LogLogJam_Supplement_nonadaptive_transcript_product
import Theorems.Thm_BosonicLearn_state_ext_characteristic
open MeasureTheory ProbabilityTheory BosonicLearn LogLogJam.Supplement Matrix Finset Filter
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Classical ENNReal Topology
set_option maxHeartbeats 1500000
namespace Mom
private def sets (u : ℕ) := (Finset.univ : Finset (Fin (2*u+1))).powersetCard (u+1)
private theorem nonemp (u : ℕ) : (sets u).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr; simp; omega
private theorem sne {u} (s : Finset (Fin (2*u+1))) (h : s∈sets u) : s.Nonempty := by
  have hs := (Finset.mem_powersetCard.mp h).2; rw [← card_pos]; omega
private noncomputable def small {u} (s : Finset (Fin (2*u+1))) (v : Fin (2*u+1) → ℝ) :=
  if h : s.Nonempty then -(s.sup' h fun i => -v i) else 0
noncomputable def median (u : ℕ) (v : Fin (2*u+1) → ℝ) := (sets u).sup' (nonemp u) (fun s => small s v)
private theorem meas_sup {α ι : Type*} [MeasurableSpace α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α → ℝ) (hm : ∀ i ∈ s, Measurable (f i)) : Measurable (fun x => s.sup' hs (fun i => f i x)) := by
  have h := Finset.measurable_sup' hs hm
  convert h using 1
  funext x; simp [Finset.sup'_apply]
theorem meas_median (u : ℕ) : Measurable (median u) := by
  unfold median
  apply meas_sup (sets u) (nonemp u) (fun s v => small s v); intro s hs
  simp only [small,dif_pos (sne s hs)]
  exact (meas_sup s (sne s hs) _ (fun i _ => (measurable_pi_apply i).neg)).neg
private theorem good {u} (a c : ℝ) (v : Fin (2*u+1) → ℝ)
    (h : (Finset.univ.filter fun i => c < |v i-a|).card ≤ u) : |median u v-a| ≤ c := by
  classical
  let bad := Finset.univ.filter fun i => c < |v i-a|
  change bad.card ≤ u at h
  have hg : u+1 ≤ (badᶜ).card := by rw [Finset.card_compl]; simp; omega
  obtain ⟨s,hs1, hsz⟩ := Finset.exists_subset_card_eq hg
  have hs : s ∈ sets u := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hsz⟩
  have hlo : a-c ≤ median u v := by
    apply le_trans _ (Finset.le_sup' (fun k => small k v) hs)
    rw [small,dif_pos (sne s hs),le_neg]
    apply Finset.sup'_le; intro i hi
    have hbi := Finset.mem_compl.mp (hs1 hi)
    have hval : |v i-a| ≤ c := by simpa [bad] using hbi
    linarith [(abs_le.mp hval).1]
  have hhi : median u v ≤ a+c := by
    apply Finset.sup'_le;intro s hs
    have hn : ¬s ⊆ bad := by
      intro hh; have hcard := Finset.card_le_card hh; have hk := (Finset.mem_powersetCard.mp hs).2;omega
    obtain ⟨i,hi,hnot⟩ := Finset.not_subset.mp hn
    have hv : |v i-a| ≤ c := by simpa [bad] using hnot
    rw [small,dif_pos (sne s hs)]
    have hl := Finset.le_sup' (fun j => -v j) hi
    linarith [(abs_le.mp hv).2]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem median_bad {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (u : ℕ) (f : Ω → ℝ) (a c : ℝ) (h : ν {x | c < |f x-a|} ≤ 1/16) :
    (Measure.pi fun _ : Fin (2*u+1) => ν) {x | c < |median u (fun i => f (x i)) - a|} ≤ (1/4:ℝ≥0∞)^u := by
  classical
  let bad := {x | c < |f x-a|}
  let rect (s : Finset (Fin (2*u+1))) := Set.univ.pi (fun i => if i∈s then bad else Set.univ)
  have inc : {x | c < |median u (fun i => f (x i)) -a|} ⊆ ⋃ s ∈ sets u, rect s := by
    intro x hx
    have hn : ¬ (Finset.univ.filter fun i => c < |f (x i)-a|).card ≤ u := fun hc => (not_lt_of_ge (good a c _ hc)) hx
    obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ.filter fun i => c < |f (x i)-a|) (show u+1 ≤ _ by omega)
    refine Set.mem_iUnion₂.mpr ⟨s,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩,?_⟩
    intro i _; change x i ∈ (if i∈s then bad else Set.univ); split_ifs with hi
    · exact (Finset.mem_filter.mp (hs hi)).2
    · trivial
  have prob (s) (hs : s∈sets u) : (Measure.pi fun _ : Fin (2*u+1) => ν) (rect s) ≤ (1/16:ℝ≥0∞)^(u+1) := by
    dsimp only [rect]; rw [Measure.pi_pi]
    simp only [apply_ite ν,measure_univ,Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_const,(Finset.mem_powersetCard.mp hs).2]
    exact pow_le_pow_left' h _
  calc
    _ ≤ _ := measure_mono inc
    _ ≤ _ := measure_biUnion_finset_le (sets u) rect
    _ ≤ ∑ _s ∈ sets u, (1/16:ℝ≥0∞)^(u+1) := Finset.sum_le_sum (fun s hs => prob s hs)
    _ = ((2*u+1).choose (u+1):ℝ≥0∞) * (1/16:ℝ≥0∞)^(u+1) := by simp [sets, nsmul_eq_mul]
    _ ≤ (2:ℝ≥0∞)^(2*u+1) * (1/16:ℝ≥0∞)^(u+1) := by gcongr; exact_mod_cast Nat.choose_le_two_pow _ _
    _ ≤ _ := by
      rw [pow_succ,pow_succ,pow_mul]; rw [show (2:ℝ≥0∞)^2=4 by norm_num]
      calc
        _ = ((4:ℝ≥0∞)*(1/16))^u *(2*(1/16)) := by rw [mul_pow]; ac_rfl
        _ ≤ _ := by
          have h4 : (4:ℝ≥0∞)*(1/16) = 1/4 := by apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp; norm_num
          rw [h4]; exact mul_le_of_le_one_right (by positivity) (by apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num)
end Mom

namespace Mom
noncomputable def avg (b : ℕ) (x : Fin b → ℝ) := (b:ℝ)⁻¹ * ∑ i, x i

theorem block_bad (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℕ) (hb : 0 < b)
    (a σ c : ℝ) (h2 : MemLp id 2 ν) (hm : ∫ x, x ∂ν = a) (hv : variance id ν ≤ 2*σ^2)
    (hσ0 : 0 ≤ σ) (hc : 0 < c) (hsize : 32 ≤ b * c^2) :
    (Measure.pi fun _ : Fin b => ν) {x | c*σ < |avg b x-a|} ≤ 1/16 := by
  let μ := Measure.pi (fun _ : Fin b => ν)
  let Z := fun x : Fin b → ℝ => ∑ i, x i
  have hb' : 0 < (b:ℝ) := by exact_mod_cast hb
  have hzm : MemLp Z 2 μ := memLp_finset_sum _ fun i _ => h2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin b => ν) i)
  have ham : MemLp (avg b) 2 μ := hzm.const_mul _
  have hz (i : Fin b) : ∫ x, x i ∂μ = a := by
    have h := measurePreserving_eval (fun _ : Fin b => ν) i
    rw [← hm,← h.map_eq,integral_map h.measurable.aemeasurable (by fun_prop)]
  have ha : ∫ x, avg b x ∂μ = a := by
    simp only [avg,integral_const_mul]
    rw [integral_finsetSum (μ:=μ) (f:=fun (i : Fin b) (x : Fin b → ℝ) => x i) Finset.univ (fun i _ => (h2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin b => ν) i)).integrable (by norm_num))]
    simp [hz,hb'.ne']
  have hvar : variance (avg b) μ ≤ (b:ℝ)⁻¹ * (2*σ^2) := by
    change variance (fun x => (b:ℝ)⁻¹ * Z x) μ ≤ _
    rw [variance_const_mul]
    have e : variance Z μ = (b:ℝ)*variance id ν := by
      have e := variance_sum_pi (μ := fun _ : Fin b => ν) (X := fun _ => id) (fun _ => h2)
      have he : (∑ i : Fin b, (fun x : Fin b → ℝ => id (x i))) = Z := by ext x; simp [Z,Finset.sum_apply]
      rw [he] at e; simpa [μ,nsmul_eq_mul] using e
    rw [e]; calc
      _ = (b:ℝ)⁻¹ * variance id ν := by field_simp
      _ ≤ _ := by gcongr
  rcases hσ0.eq_or_lt with hσ | hσ
  · subst σ
    have he : variance (avg b) μ = 0 := le_antisymm (by simpa using hvar) (variance_nonneg _ _)
    have hzero := ae_eq_integral_of_variance_eq_zero ham he
    rw [ha] at hzero
    have hz0 : μ {x | c*0 < |avg b x-a|} = 0 := by
      apply measure_mono_null (t := {x | avg b x ≠ a}) _ (ae_iff.mp hzero)
      intro x hx h; simpa [h] using hx
    exact hz0.le.trans (bot_le)
  have ht := meas_ge_le_variance_div_sq ham (mul_pos hc hσ)
  rw [ha] at ht
  refine (measure_mono (μ:=μ) (show {x | c*σ < |avg b x-a|} ⊆ {x | c*σ ≤ |avg b x-a|} from by intro x hx; exact (show c*σ < |avg b x-a| from hx).le)).trans (ht.trans ?_)
  calc
    ENNReal.ofReal (variance (avg b) μ / (c*σ)^2) ≤ ENNReal.ofReal ((b:ℝ)⁻¹ * (2*σ^2)/(c*σ)^2) := by gcongr
    _ ≤ ENNReal.ofReal (1/16) := by
      apply ENNReal.ofReal_le_ofReal; rw [inv_mul_eq_div]; field_simp; nlinarith [mul_le_mul_of_nonneg_right hsize (sq_nonneg σ)]
    _ = _ := by apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp; norm_num
end Mom

namespace Mom
private theorem select {I J : Type} [Fintype I] [Fintype J] (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (g : J → I) (hg : Function.Injective g) :
    MeasurePreserving (fun (x : I → ℝ) j => x (g j)) (Measure.pi μ) (Measure.pi fun j => μ (g j)) := by
  have h : iIndepFun (fun i (x : I → ℝ) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X:=fun _ => id) (fun _ => aemeasurable_id)
  have hj := h.precomp hg
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (measurable_pi_apply (g j)).aemeasurable)).mp hj
  simp_rw [(measurePreserving_eval μ _).map_eq] at he
  exact ⟨measurable_pi_lambda _ (fun j => measurable_pi_apply _),he⟩

private theorem flat {I J : Type} [Fintype I] [Fintype J] (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun (x : I → J → ℝ) (ij : I×J) => x ij.1 ij.2)
      (Measure.pi fun _ : I => Measure.pi fun _ : J => ν) (Measure.pi fun _ : I×J => ν) := by
  have hm : Measurable (fun (x : I → J → ℝ) (ij : I×J) => x ij.1 ij.2) := by fun_prop
  refine ⟨hm,(Measure.pi_eq ?_).symm⟩
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : I → J → ℝ) (ij : I×J) => x ij.1 ij.2) ⁻¹' Set.univ.pi s =
    Set.univ.pi (fun i => Set.univ.pi (fun j => s (i,j))) := by ext x; simp [Set.mem_univ_pi,Prod.forall]
  rw [he,Measure.pi_pi]; simp_rw [Measure.pi_pi]; rw [Fintype.prod_prod_type]

theorem blocks {I J K : Type} [Fintype I] [Fintype J] [Fintype K] (μ : K → Measure ℝ)
    [∀ k, IsProbabilityMeasure (μ k)] (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : I×J → K)
    (hg : Function.Injective g) (he : ∀ i j, μ (g (i,j)) = ν) :
    MeasurePreserving (fun (x : K → ℝ) i j => x (g (i,j))) (Measure.pi μ) (Measure.pi fun _ : I => Measure.pi fun _ : J => ν) := by
  have h := select μ g hg
  have hv : (fun p => μ (g p)) = (fun _ : I × J => ν) := by funext p;exact he p.1 p.2
  rw [hv] at h
  let e : (I → J → ℝ) ≃ᵐ (I×J → ℝ) := ⟨(Equiv.curry I J ℝ).symm, by exact measurable_pi_lambda _ fun ij => (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1), by exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_apply (i,j)⟩
  have he' : MeasurePreserving e (Measure.pi fun _ : I => Measure.pi fun _ : J => ν) (Measure.pi fun _ : I×J => ν) := flat ν
  exact he'.symm.comp h
end Mom
namespace Mom
private theorem budget (η δ : ℝ) (m : ℕ) (hη : 0 < η) (hη' : η ≤ 1/4) (hδ : 0 < δ) (hδ' : δ < 1)
    (hm : 1024 * Real.log (2/δ) / η^2 ≤ m) :
    let b := ⌈32/η^2⌉₊; let u := ⌈Real.log (2/δ)⌉₊
    0 < b ∧ 32 ≤ (b:ℝ)*η^2 ∧ m/2+(2*u+1)*b ≤ m ∧ (1/4:ℝ≥0∞)^u ≤ ENNReal.ofReal δ := by
  let b := ⌈32/η^2⌉₊; let u := ⌈Real.log (2/δ)⌉₊; let l := Real.log (2/δ)
  change 0 < b ∧ 32 ≤ (b:ℝ)*η^2 ∧ m/2+(2*u+1)*b ≤ m ∧ (1/4:ℝ≥0∞)^u ≤ ENNReal.ofReal δ
  have h2 : 2 ≤ 2/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hl : 1/2 ≤ l := (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans (Real.log_le_log (by norm_num) h2)
  have hb := Nat.le_ceil (32/η^2); have hu := Nat.le_ceil l
  have hbs : 32 ≤ (b:ℝ)*η^2 := (div_le_iff₀ (sq_pos_of_pos hη)).mp hb
  have hbpos : 0 < b := Nat.ceil_pos.mpr (by positivity)
  have hbt : (b:ℝ) ≤ 32/η^2+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hut : (u:ℝ) ≤ l+1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hems : η^2 ≤ 1 := by nlinarith [sq_nonneg (η-1/4),mul_nonneg hη.le (sub_nonneg.mpr hη')]
  have hup : 2*(u:ℝ)+1 ≤ 8*l := by linarith
  have hbup : (b:ℝ)*η^2 ≤ 33 := by have hh := mul_le_mul_of_nonneg_right hbt (sq_nonneg η);field_simp [hη.ne'] at hh; nlinarith
  have hm' := (div_le_iff₀ (sq_pos_of_pos hη)).mp hm
  have hc : 2*((2*(u:ℝ)+1)*(b:ℝ)) ≤ m := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hη)).mp
    have hh := mul_le_mul hup hbup (mul_nonneg (by positivity) (sq_nonneg η)) (by linarith)
    change 1024*l ≤ _ at hm'; nlinarith
  have hcn : 2*((2*u+1)*b) ≤ m := by exact_mod_cast hc
  refine ⟨hbpos,hbs,by omega,?_⟩
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hδ.le]
  have hlog : 1 ≤ Real.log 4 := by rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)];linarith [Real.log_two_gt_d9]
  apply (Real.log_le_log_iff (by positivity) hδ).mp
  rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  have hu' : Real.log 2 - Real.log δ ≤ (u:ℝ) := by calc
    _ = l := (Real.log_div (by norm_num) hδ.ne').symm
    _ ≤ _ := hu
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg u), Real.log_pos (by norm_num : (1:ℝ)<2)]

theorem robust (η δ : ℝ) (m : ℕ) (hη : 0 < η) (hη' : η ≤ 1/4) (hδ : 0 < δ) (hδ' : δ < 1)
    (hm : 1024*Real.log (2/δ)/η^2 ≤ m) :
    ∃ mean : (Fin m → ℝ) → ℝ, Measurable mean ∧ (∀ x, 0 ≤ mean x) ∧
    (∀ x y, (∀ i : Fin m, m/2 ≤ i.val → x i = y i) → mean x = mean y) ∧
    ∀ (μ : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∀ i : Fin m, m/2 ≤ i.val → μ i = ν) →
      ∀ (a σ : ℝ), 0 ≤ a → 0 ≤ σ → MemLp id 2 ν → (∫ x, x ∂ν) = a → variance id ν ≤ 2*σ^2 →
        (Measure.pi μ) {x | η*σ < |mean x-a|} ≤ ENNReal.ofReal δ := by
  classical
  let b := ⌈32/η^2⌉₊; let u := ⌈Real.log (2/δ)⌉₊
  obtain ⟨hb,hsize,hm',hprob⟩ := budget η δ m hη hη' hδ hδ' hm
  change m/2+(2*u+1)*b ≤ m at hm'
  let g (ij : Fin (2*u+1) × Fin b) : Fin m := ⟨m/2 + (finProdFinEquiv ij).val,by have := (finProdFinEquiv ij).isLt;omega⟩
  have hg : Function.Injective g := by
    intro a b hh; apply finProdFinEquiv.injective; apply Fin.ext; have h := congrArg Fin.val hh;dsimp [g] at h;omega
  let F (x : Fin m → ℝ) := fun (i : Fin (2*u+1)) (j : Fin b) => x (g (i,j))
  let est (x : (Fin (2*u+1)) → Fin b → ℝ) := median u (fun i => avg b (x i))
  have hest : Measurable est := (meas_median u).comp (measurable_pi_lambda _ fun i => by unfold avg;fun_prop)
  refine ⟨fun x => max 0 (est (F x)),measurable_const.max (hest.comp (by unfold F;fun_prop)),fun _ => le_max_left _ _,?_,?_⟩
  · intro x y h;have hh : F x = F y := by funext i j;exact h _ (Nat.le_add_right _ _)
    change max 0 (est (F x)) = max 0 (est (F y));rw [hh]
  · intro μ _ ν _ hμ a σ ha hσ h2 hmean hvar
    have hmp := blocks μ ν g hg (fun i j => hμ _ (Nat.le_add_right _ _))
    have hevent : MeasurableSet {x | η*σ < |est x-a|} := measurableSet_lt measurable_const (hest.sub_const a).abs
    have incl : {x | η*σ < |max 0 (est (F x))-a|} ⊆ F ⁻¹' {x | η*σ < |est x-a|} := by
      intro x hx;change η*σ < |est (F x)-a|; by_cases h : 0 ≤ est (F x)
      · simpa [max_eq_right h] using hx
      · simp only [Set.mem_setOf_eq,max_eq_left (le_of_not_ge h),zero_sub,abs_neg,abs_of_nonneg ha] at hx
        rw [abs_of_nonpos (by linarith : est (F x)-a ≤ 0)];linarith
    refine (measure_mono incl).trans ?_;rw [show (Measure.pi μ) (F ⁻¹' {x | η*σ < |est x-a|}) = _ from hmp.measure_preimage hevent.nullMeasurableSet]
    exact (median_bad _ u (avg b) a (η*σ) (block_bad ν b hb a σ η h2 hmean hvar hσ hη hsize)).trans hprob
end Mom

namespace Counts
noncomputable def wt (r : ℝ) (j : ℕ) : ℝ := (1/Real.cosh r) * ((j.centralBinom:ℝ)/4^j * (Real.tanh r ^ 2)^j)
private theorem wt_nn r j : 0 ≤ wt r j := by dsimp [wt]; positivity
private theorem tc (r : ℝ) : 1-Real.tanh r^2 = (Real.cosh r^2)⁻¹ := by rw [Real.tanh_eq_sinh_div_cosh];field_simp [(Real.cosh_pos r).ne'];nlinarith [Real.cosh_sq_sub_sinh_sq r]
private theorem sum_pow (r : ℝ) (k : ℕ) : Summable (fun j : ℕ => (j:ℝ)^k * wt r j) := by
  let q := Real.tanh r ^2
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];have hg := tc r;have := inv_pos.mpr (sq_pos_of_pos (Real.cosh_pos r));dsimp [q];linarith
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (wt_nn _ _)) _ ((summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) k hq).mul_left (1/Real.cosh r))
  intro j
  have hw : (j.centralBinom:ℝ)/4^j ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.centralBinom_le_four_pow j)
  change (j:ℝ)^k*((1/Real.cosh r)*(_ * q^j)) ≤ (1/Real.cosh r)*((j:ℝ)^k*q^j)
  calc
    _ ≤ (j:ℝ)^k*((1/Real.cosh r)*(1 * q^j)) := by gcongr
    _ = _ := by ring
private theorem rec_wt (r : ℝ) (j : ℕ) : ((j:ℝ)+1)*wt r (j+1) = (Real.tanh r)^2*((j:ℝ)+1/2)*wt r j := by
  have h : ((j:ℝ)+1) * ((j+1).centralBinom:ℝ) = 2*(2*(j:ℝ)+1)*(j.centralBinom:ℝ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ j
  dsimp [wt];rw [pow_succ,pow_succ (Real.tanh r ^2)];field_simp;linear_combination 2*h*(Real.tanh r^2)^j*(Real.tanh r^2)

theorem moments (r : ℝ) (hzero : HasSum (wt r) 1) :
    HasSum (fun j : ℕ => (2*(j:ℝ))*wt r j) (Real.sinh r^2) ∧
    HasSum (fun j : ℕ => (2*(j:ℝ))^2*wt r j) (2*(Real.sinh r*Real.cosh r)^2+(Real.sinh r^2)^2) := by
  let q := Real.tanh r^2
  let m := ∑' j : ℕ, (j:ℝ)*wt r j
  let m2 := ∑' j : ℕ, (j:ℝ)^2*wt r j
  have h1 : HasSum (fun j : ℕ => (j:ℝ)*wt r j) m := by simpa [m] using (sum_pow r 1).hasSum
  have h2 : HasSum (fun j : ℕ => (j:ℝ)^2*wt r j) m2 := (sum_pow r 2).hasSum
  have sh1 : HasSum (fun j : ℕ => ((j:ℝ)+1)*wt r (j+1)) m := by simpa using (hasSum_nat_add_iff' 1).mpr h1
  have sh2 : HasSum (fun j : ℕ => ((j:ℝ)+1)^2*wt r (j+1)) m2 := by simpa using (hasSum_nat_add_iff' 1).mpr h2
  have e1 : m = q*(m+1/2) := by
    apply sh1.unique
    have f : (fun j : ℕ => ((j:ℝ)+1)*wt r (j+1)) = fun (j:ℕ) => q*((j:ℝ)*wt r j+(1/2)*wt r j) := by funext j; rw [rec_wt]; dsimp [q];ring
    rw [f]; simpa only [mul_one] using ((h1.add (hzero.mul_left (1/2))).mul_left q)
  have e2 : m2 = q*(m2+3/2*m+1/2) := by
    apply sh2.unique
    have f : (fun j : ℕ => ((j:ℝ)+1)^2*wt r (j+1)) = fun (j:ℕ) => q*((j:ℝ)^2*wt r j+(3/2)*((j:ℝ)*wt r j)+(1/2)*wt r j) := by funext j; rw [pow_two,mul_assoc,rec_wt]; dsimp [q];ring
    rw [f];simpa only [mul_one] using (((h2.add (h1.mul_left (3/2))).add (hzero.mul_left (1/2))).mul_left q)
  have hq : (1-q)*Real.cosh r^2=1 := by dsimp [q];rw [tc,inv_mul_cancel₀ (pow_ne_zero 2 (Real.cosh_pos r).ne')]
  have hqc : q * Real.cosh r^2 = Real.sinh r^2 := by dsimp [q];rw [Real.tanh_eq_sinh_div_cosh, div_pow,div_mul_cancel₀ _ (pow_ne_zero 2 (Real.cosh_pos r).ne')]
  have a : 2*m = Real.sinh r^2 := by linear_combination (2*Real.cosh r^2)*e1 - (2*m)*hq + hqc
  have z : 4*m2 = 2*(Real.sinh r*Real.cosh r)^2 + (Real.sinh r^2)^2 := by
    linear_combination (4*Real.cosh r^2)*e2 - (4*m2)*hq + (6*m+2)*hqc + 3*(Real.sinh r^2)*a - 2*(Real.sinh r^2)*(Real.cosh_sq_sub_sinh_sq r)
  constructor
  · rw [← a]; have f : (fun j : ℕ => (2*(j:ℝ))*wt r j) = fun (j:ℕ) => 2*((j:ℝ)*wt r j) := by funext j;ring
    rw [f];exact h1.mul_left 2
  · rw [← z]; have f : (fun j : ℕ => (2*(j:ℝ))^2*wt r j) = fun (j:ℕ) => 4*((j:ℝ)^2*wt r j) := by funext j;ring
    rw [f];exact h2.mul_left 4
@[irreducible] private noncomputable def wAmp (r θ : ℝ) (n : ℕ) : ℂ :=
  if Even n then ((Real.sqrt ((n/2).centralBinom : ℝ) / ((2:ℝ)^(n/2) * Real.sqrt (Real.cosh r)) : ℝ) : ℂ) *
    ((Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ) * Complex.I))^(n/2) else 0

private theorem sq_n (r θ : ℝ) (j : ℕ) : ‖wAmp r θ (2*j)‖^2 =
    1/Real.cosh r * ((j.centralBinom:ℝ)/4^j * (Real.tanh r ^ 2)^j) := by
  have c := (Real.cosh_pos r).le
  simp only [wAmp, even_two_mul, if_true, Nat.mul_div_cancel_left _ (by decide : 0<2),norm_mul,norm_pow,
    Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs, mul_pow, ← Nat.pow_mul, ← sq_abs,
    sq_abs, div_pow,Real.sq_sqrt c,Real.sq_sqrt (Nat.cast_nonneg _)]
  have h : |Real.tanh r| ^ (j*2) = Real.tanh r ^ (j*2) := by rw [Nat.mul_comm, pow_mul, sq_abs, ← pow_mul]
  ring_nf; rw [h, show ((2:ℝ)⁻¹)^(j*2) = (4⁻¹:ℝ)^j by rw [Nat.mul_comm, pow_mul]; norm_num]

private theorem numLaw (M : FockPOVM (Occupation (Fin 1)) ℝ) (hM : ∀ B : Set ℝ, MeasurableSet B → ∀ i j,
      M.effect B i j = if i = j ∧ (i 0 : ℝ) ∈ B then 1 else 0)
    (ρ : State (Occupation (Fin 1))) (r θ : ℝ) (hρ : squeezedAt ρ r θ) :
    M.law ρ.coefficients = Measure.sum (fun j : ℕ => ENNReal.ofReal (wt r j) • Measure.dirac (2*(j:ℝ))) := by
  classical
  obtain ⟨s,hs,hcoef⟩ := squeezed_fock_realization r θ hρ.1
  have hsame := state_ext_characteristic ρ s (fun ξ => (hρ.2.2 ξ).trans (hs.2.2 ξ).symm)
  have hc (i j : Occupation (Fin 1)) : ρ.coefficients i j = wAmp r θ (i 0) * star (wAmp r θ (j 0)) := by rw [hsame];simpa only [wAmp] using hcoef i j
  ext B hB
  rw [M.law_born _ ρ.density _ hB,Measure.sum_apply _ hB]
  let ix (n : ℕ) : Occupation (Fin 1) := fun _ => 2*n
  have hix : Function.Injective ix := by intro n m h; have h' := congrFun h 0;change 2*n=2*m at h';omega
  have hinner (i : Occupation (Fin 1)) : (∑' j, M.effect B i j * ρ.coefficients j i) =
      if (i 0:ℝ)∈B then ((‖wAmp r θ (i 0)‖^2 : ℝ) : ℂ) else (0:ℂ) := by
    rw [tsum_eq_single i (by intro j hj; simp [hM B hB i j,hj.symm])];rw [hM B hB i i,hc];split_ifs <;> simp_all [Complex.mul_conj,Complex.sq_norm]
  simp_rw [hinner]
  have hoff (i : Occupation (Fin 1)) (hi : i ∉ Set.range ix) : wAmp r θ (i 0) = 0 := by
    have he : ¬Even (i 0) := by rintro ⟨a,ha⟩;apply hi;refine ⟨a,?_⟩;funext j;fin_cases j;change 2*a=i 0;omega
    simp [wAmp,he]
  rw [← hix.tsum_eq (f:=fun i : Occupation (Fin 1) => if (i 0:ℝ)∈B then ((‖wAmp r θ (i 0)‖^2:ℝ):ℂ) else 0)
    (by intro i hi;by_contra h; apply hi; simp [hoff i h])]
  have he (j : ℕ) : (if ((ix j 0:ℕ):ℝ)∈B then ((‖wAmp r θ (ix j 0)‖^2:ℝ):ℂ) else 0) = ((if (2*(j:ℝ))∈B then wt r j else 0 : ℝ):ℂ) := by
    dsimp [ix];rw [sq_n];simp only [Nat.cast_mul,Nat.cast_ofNat];split_ifs <;> simp [wt]
  simp_rw [he]; rw [← Complex.ofReal_tsum,Complex.ofReal_re]
  let v := fun j : ℕ => if 2*(j:ℝ)∈B then wt r j else 0
  have hv (j) : 0 ≤ v j := by dsimp [v];split_ifs <;> first | exact wt_nn _ _ | simp
  have hvsum : Summable v := Summable.of_nonneg_of_le hv (fun j => by change (if 2*(j:ℝ)∈B then wt r j else 0) ≤ wt r j;split_ifs <;> first | exact le_rfl | exact wt_nn _ _) (show Summable (wt r) from by simpa using sum_pow r 0)
  change ENNReal.ofReal (∑' j, v j) = _
  rw [ENNReal.ofReal_tsum_of_nonneg hv hvsum];apply tsum_congr;intro j
  simp [v,Measure.smul_apply,Measure.dirac_apply' _ hB, Set.indicator_apply];split_ifs <;> simp
private noncomputable def dist (r : ℝ) : Measure ℝ := Measure.sum (fun j : ℕ => ENNReal.ofReal (wt r j) • Measure.dirac (2*(j:ℝ)))
private theorem count_stats (r : ℝ) [IsProbabilityMeasure (dist r)] : MemLp id 2 (dist r) ∧
    (∫ x, x ∂dist r) = Real.sinh r^2 ∧ variance id (dist r) = 2*(Real.cosh r*Real.sinh r)^2 := by
  have hsum : HasSum (wt r) 1 := by
    have hu := measure_univ (μ:=dist r)
    unfold dist at hu;rw [Measure.sum_apply _ MeasurableSet.univ] at hu
    simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one] at hu
    have hs : Summable (wt r) := by simpa using sum_pow r 0
    rw [← ENNReal.ofReal_tsum_of_nonneg (wt_nn r) hs] at hu
    have := congrArg ENNReal.toReal hu
    apply hs.hasSum_iff.mpr
    simpa only [ENNReal.toReal_ofReal (tsum_nonneg (wt_nn r)), ENNReal.toReal_one] using this
  obtain ⟨h1,h2⟩ := moments r hsum
  have hls : MemLp id 2 (dist r) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
    simpa only [id_eq,Pi.pow_apply,Real.norm_eq_abs,sq_abs,abs_sq,ENNReal.toReal_ofReal (wt_nn r _),mul_comm] using h2.summable
  have first : (∫ x, x ∂dist r) = Real.sinh r^2 := by
    rw [dist,integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)]
    simpa only [smul_eq_mul,ENNReal.toReal_ofReal (wt_nn r _),mul_comm] using h1.tsum_eq
  have second : (∫ x, x^2 ∂dist r) = 2*(Real.sinh r*Real.cosh r)^2+(Real.sinh r^2)^2 := by
    rw [dist,integral_sum_dirac (fun j => ENNReal.ofReal_ne_top)]
    simpa only [smul_eq_mul,ENNReal.toReal_ofReal (wt_nn r _),mul_comm] using h2.tsum_eq
  refine ⟨hls,first,?_⟩
  rw [variance_eq_sub hls]
  change (∫ x, x^2 ∂dist r) -(∫ x, x ∂dist r)^2 = _
  rw [first,second];ring
end Counts
theorem solution :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∀ S : BosonicLearn.AdaptiveScheme 1 m ℝ, phaseCountReadouts S →
    ∃ mean : (Fin m → ℝ) → ℝ, Measurable mean ∧ (∀ x, 0 ≤ mean x) ∧
      (∀ x y, (∀ i : Fin m, m / 2 ≤ i.val → x i = y i) → mean x = mean y) ∧
      ∀ (ρ : State (Occupation (Fin 1))) (r θ : ℝ), squeezedAt ρ r θ →
        BosonicLearn.transcriptLaw S ρ.coefficients
          {x | η * Real.cosh r * Real.sinh r < |mean x - Real.sinh r ^ 2|} ≤ ENNReal.ofReal δ := by
  refine ⟨1024,by norm_num,?_⟩
  intro η δ hη hη' hδ hδ' m hm S hS
  obtain ⟨est,hmest,hpos,honly,he⟩ := Mom.robust η δ m hη hη' hδ hδ' hm
  refine ⟨est,hmest,hpos,honly,?_⟩
  intro ρ r θ hρ
  let μ := fun (i : Fin m) => (S.povm i (fun _ => 0)).law ρ.coefficients
  letI (i : Fin m) : IsProbabilityMeasure (μ i) := (S.povm i _).law_prob _ ρ.density
  have htr : BosonicLearn.transcriptLaw S ρ.coefficients = Measure.pi μ := nonadaptive_transcript_product S ρ hS.1
  have heq (i : Fin m) (hi : m/2 ≤ i.val) : μ i = Counts.dist r := Counts.numLaw _ (hS.2.2 i hi (fun _ => 0)) ρ r θ hρ
  have hbnd : 0 < 1024*Real.log (2/δ)/η^2 := by have hl : 1 < 2/δ := (lt_div_iff₀ hδ).mpr (by linarith); exact div_pos (mul_pos (by norm_num) (Real.log_pos hl)) (sq_pos_of_pos hη)
  have hmpos : 0 < m := by exact_mod_cast hbnd.trans_le hm
  let i : Fin m := ⟨m/2,Nat.div_lt_self hmpos (by decide)⟩
  letI : IsProbabilityMeasure (Counts.dist r) := heq i le_rfl ▸ (inferInstance : IsProbabilityMeasure (μ i))
  obtain ⟨h2,hfirst,hvar⟩ := Counts.count_stats r
  rw [htr,mul_assoc]
  exact he μ (Counts.dist r) heq (Real.sinh r^2) (Real.cosh r*Real.sinh r) (sq_nonneg _)
    (mul_nonneg (Real.cosh_pos r).le (Real.sinh_nonneg_iff.mpr hρ.1)) h2 hfirst hvar.le
