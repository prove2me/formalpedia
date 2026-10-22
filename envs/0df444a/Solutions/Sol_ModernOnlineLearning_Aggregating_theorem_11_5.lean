-- Prove2me | solution 1 for ModernOnlineLearning.Aggregating.theorem_11_5
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T08:15:17.876995+00:00
-- url     : https://prove2.me/submissions/7c3984fc-fa99-4c67-ad1e-e484d565c92c

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint
import Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
import Definitions.Def_ModernOnlineLearning_Aggregating_ShrunkSet
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

private lemma concave_average_le_of_continuousAt
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure Ω} [IsFiniteMeasure μ] [NeZero μ]
    {V : Set E} {g : E → ℝ} {f : Ω → E}
    (hg : ConcaveOn ℝ V g) (hf : ∀ᵐ x ∂μ, f x ∈ V)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ)
    (hc : ContinuousAt g (⨍ x, f x ∂μ)) :
    (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ) := by
  let H : Set (E × ℝ) := {p | p.1 ∈ V ∧ p.2 ≤ g p.1}
  have hmem : ∀ᵐ x ∂μ, (f x,g (f x)) ∈ closure H :=
    hf.mono (fun x hx => subset_closure ⟨hx,le_rfl⟩)
  have hp : (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ closure H := by
    exact average_pair hfi hgi ▸
      hg.convex_hypograph.closure.average_mem isClosed_closure hmem (hfi.prodMk hgi)
  let p : E × ℝ := (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ)
  have : NeBot (𝓝[H] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hcont : ContinuousAt (fun z : E × ℝ => g z.1-z.2) p :=
    (ContinuousAt.comp (f := Prod.fst) (x := p) hc continuous_fst.continuousAt).sub continuous_snd.continuousAt
  have hnonneg : ∀ᶠ z in 𝓝[H] p, 0 ≤ g z.1-z.2 :=
    (show ∀ᶠ z in 𝓝[H] p, z ∈ H from self_mem_nhdsWithin).mono
      (fun z hz => sub_nonneg.mpr hz.2)
  have he := isClosed_Ici.mem_of_tendsto (hcont.mono_left nhdsWithin_le_nhds) hnonneg
  exact sub_nonneg.mp he

private lemma nonneg_concave_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Set E} {g : E → ℝ}
    (hg : ConcaveOn ℝ V g) (hgn : ∀ x ∈ V, 0 ≤ g x)
    (hVi : (interior V).Nonempty) (hVb : Bornology.IsBounded V) :
    ∃ M : ℝ, ∀ x ∈ V, g x ≤ M := by
  obtain ⟨c,hc⟩ := hVi
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
  obtain ⟨R,hR,hRV⟩ := hVb.subset_closedBall_lt 0 c
  let b := r/(2*R)
  have hb : 0 < b := by dsimp [b];positivity
  let a := b/(1+b)
  let β := 1/(1+b)
  have ha : 0 < a := by dsimp [a];positivity
  have hβ : 0 < β := by dsimp [β];positivity
  have hab : a+β=1 := by dsimp [a,β];field_simp;ring
  have habb : a=β*b := by dsimp [a,β];ring
  refine ⟨g c/a,?_⟩
  intro x hx
  let y := c-b • (x-c)
  have hy : y ∈ V := by
    apply hrV
    rw [mem_ball,dist_eq_norm]
    have hyc : y-c = -(b • (x-c)) := by dsimp [y];module
    rw [hyc,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hb]
    have hxR := hRV hx
    rw [mem_closedBall,dist_eq_norm] at hxR
    calc b*‖x-c‖ ≤ b*R := mul_le_mul_of_nonneg_left hxR hb.le
      _ = r/2 := by dsimp [b];field_simp
      _ < r := by linarith
  have hccomb : a • x+β • y=c := by
    calc
      a • x+β • y = (a-β*b) • x+(β+β*b) • c := by dsimp [y];module
      _ = c := by rw [← habb,sub_self,zero_smul,zero_add,add_comm β a,hab,one_smul]
  have h := hg.2 hx hy ha.le hβ.le hab
  rw [hccomb] at h
  simp only [smul_eq_mul] at h
  apply (le_div_iff₀ ha).mpr
  have hp := mul_nonneg hβ.le (hgn y hy)
  simpa [mul_comm] using (show a*g x ≤ g c by linarith)

private lemma average_mem_interior_of_volume_ac
    {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ]
    (hV : Convex ℝ V) (hVi : (interior V).Nonempty)
    (hac : volume.restrict V ≪ μ)
    (hmem : ∀ᵐ x ∂μ, x ∈ V) (hi : Integrable (fun x => x) μ) :
    (⨍ x, x ∂μ) ∈ interior V := by
  obtain ⟨c,hc⟩ := hVi
  obtain ⟨r,hr,hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_interior.mem_nhds hc)
  have hB : closedBall c r ⊆ V := hrV.trans interior_subset
  have hpos : μ (closedBall c r) ≠ 0 := by
    intro hz
    have hz' := hac hz
    rw [Measure.restrict_apply isClosed_closedBall.measurableSet,
      inter_eq_left.mpr hB] at hz'
    exact (Metric.measure_closedBall_pos volume c hr).ne' hz'
  apply hV.average_mem_interior_of_set hpos hmem hi
  apply hrV
  exact (convex_closedBall c r).set_average_mem isClosed_closedBall hpos
    (measure_ne_top _ _) (ae_restrict_mem isClosed_closedBall.measurableSet) hi.integrableOn

private lemma weighted_concave_average
    {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}
    {w g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : Convex ℝ V) (hVc : IsClosed V) (hVb : Bornology.IsBounded V)
    (hVp : 0 < volume V) (hg : ConcaveOn ℝ V g)
    (hgp : ∀ x ∈ V, 0 ≤ g x) (hwp : ∀ x ∈ V, 0 < w x)
    (hgm : AEMeasurable g (volume.restrict V))
    (hwi : IntegrableOn w V)
    (hxi : IntegrableOn (fun x => w x • x) V) :
    0 < (∫ x in V, w x) ∧
    IntegrableOn (fun x => w x * g x) V ∧
    (∫ x in V, w x * g x) / (∫ x in V, w x) ≤
      g ((∫ x in V, w x)⁻¹ • ∫ x in V, w x • x) := by
  let ν := volume.restrict V
  let ρ := fun x => ENNReal.ofReal (w x)
  let μ := ν.withDensity ρ
  have hmemν : ∀ᵐ x ∂ν, x ∈ V := ae_restrict_mem hVc.measurableSet
  have hwpos : ∀ᵐ x ∂ν, 0 < w x := hmemν.mono (fun x hx => hwp x hx)
  have hwnonneg : ∀ᵐ x ∂ν, 0 ≤ w x := hwpos.mono (fun _ hx => hx.le)
  have hρm : AEMeasurable ρ ν := hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂ν, ρ x < ∞ := Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hρeq : ∀ᵐ x ∂ν, (ρ x).toReal = w x := hwnonneg.mono (fun _ hx => ENNReal.toReal_ofReal hx)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal hwnonneg).mp hwi.hasFiniteIntegral).ne
  have hac : μ ≪ ν := withDensity_absolutelyContinuous ν ρ
  have hac' : ν ≪ μ := withDensity_absolutelyContinuous' hρm
    (hwpos.mono (fun _ hx => (ENNReal.ofReal_pos.mpr hx).ne'))
  have hμne : μ ≠ 0 := by
    intro hz
    have he : ν Set.univ = 0 := hac' (by simp [hz])
    exact hVp.ne' (by simpa [ν] using he)
  let : NeZero μ := ⟨hμne⟩
  have hmemμ : ∀ᵐ x ∂μ, x ∈ V := hac.ae_le hmemν
  have hVi : (interior V).Nonempty := by
    by_contra hn
    have he : interior V = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hfront := hV.addHaar_frontier volume
    rw [frontier, hVc.closure_eq, he, sdiff_empty] at hfront
    exact hVp.ne' hfront
  have hidi : Integrable (fun x => x) μ := by
    apply (integrable_withDensity_iff_integrable_smul₀' hρm hρtop).mpr
    apply hxi.congr
    exact hρeq.mono (fun x hx => by simp only [hx])
  have hmean := average_mem_interior_of_volume_ac hV hVi hac' hmemμ hidi
  obtain ⟨M,hM⟩ := nonneg_concave_bounded hg hgp hVi hVb
  have hgi : Integrable g μ := by
    apply (integrable_const (|M| : ℝ)).mono' (hgm.mono' hac).aestronglyMeasurable
    filter_upwards [hmemμ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hgp x hx)]
    exact (hM x hx).trans (le_abs_self M)
  have hprod : IntegrableOn (fun x => w x * g x) V := by
    have hi := (integrable_withDensity_iff_integrable_smul₀' hρm hρtop).mp hgi
    apply hi.congr
    exact hρeq.mono (fun x hx => by simp only [hx,smul_eq_mul])
  have hmass : μ.real Set.univ = ∫ x in V, w x := by
    calc
      _ = ∫ _x, (1 : ℝ) ∂μ := by simp
      _ = ∫ x, (ρ x).toReal • (1 : ℝ) ∂ν :=
        integral_withDensity_eq_integral_toReal_smul₀ hρm hρtop _
      _ = _ := integral_congr_ae (hρeq.mono (fun x hx => by simp [hx]))
  have hid : (∫ x, x ∂μ) = ∫ x in V, w x • x := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρm hρtop]
    exact integral_congr_ae (hρeq.mono (fun x hx => by simp only [hx]))
  have hig : (∫ x, g x ∂μ) = ∫ x in V, w x * g x := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρm hρtop]
    exact integral_congr_ae (hρeq.mono (fun x hx => by simp only [hx,smul_eq_mul]))
  refine ⟨hmass ▸ measureReal_univ_pos, hprod, ?_⟩
  have hJ := concave_average_le_of_continuousAt hg hmemμ hidi hgi
    (hg.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hmean))
  simpa only [average_eq, hmass, hid, hig, smul_eq_mul, div_eq_inv_mul] using hJ

open LogRegretOCO.EWOO ModernOnlineLearning.Aggregating

private lemma weight_succ {d : ℕ} (α : ℝ)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ewooWeight α ℓ (t+1) = fun x => ewooWeight α ℓ t x * Real.exp (-α * ℓ t x) := by
  funext x
  simp only [ewooWeight, Finset.sum_Ico_succ_top ht, mul_add, Real.exp_add]

private lemma waa_partition_upper
    {d : ℕ} (T : ℕ) (V : Set (EuclideanSpace ℝ (Fin d)))
    (hV : Convex ℝ V) (hVc : IsClosed V) (hVb : Bornology.IsBounded V)
    (hVp : 0 < volume V) (α : ℝ)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hexp : ∀ t ∈ Finset.Icc 1 T, ExpConcaveOn V α (ℓ t))
    (hmeas : ∀ t ∈ Finset.Icc 1 T, AEMeasurable (ℓ t) (volume.restrict V))
    (hwi : ∀ t ∈ Finset.Icc 1 T, IntegrableOn (ewooWeight α ℓ t) V)
    (hxi : ∀ t ∈ Finset.Icc 1 T, IntegrableOn (fun x => ewooWeight α ℓ t x • x) V) :
    IntegrableOn (ewooWeight α ℓ (T+1)) V ∧
    (∫ x in V, ewooWeight α ℓ (T+1) x) ≤
      (volume V).toReal * Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t (ewooPoint V α ℓ t)) := by
  have hJ : ∀ t ∈ Finset.Icc 1 T,
      0 < (∫ x in V, ewooWeight α ℓ t x) ∧
      IntegrableOn (ewooWeight α ℓ (t+1)) V ∧
      (∫ x in V, ewooWeight α ℓ (t+1) x) ≤
        (∫ x in V, ewooWeight α ℓ t x) * Real.exp (-α * ℓ t (ewooPoint V α ℓ t)) := by
    intro t ht
    obtain ⟨hp,hi,hj⟩ := weighted_concave_average (w := ewooWeight α ℓ t) hV hVc hVb hVp (hexp t ht)
      (fun x _ => (Real.exp_pos _).le) (fun x _ => Real.exp_pos _)
      (((hmeas t ht).const_mul (-α)).exp) (hwi t ht) (hxi t ht)
    rw [← weight_succ α ℓ t (Finset.mem_Icc.mp ht).1] at hi hj
    exact ⟨hp,hi,by simpa [ewooPoint,mul_comm] using (div_le_iff₀ hp).mp hj⟩
  have hVfin : volume V < ∞ := hVb.measure_lt_top
  have hwone : ewooWeight α ℓ 1 = fun _ => 1 := by funext x;simp [ewooWeight]
  have hbase : IntegrableOn (ewooWeight α ℓ 1) V := by
    rw [hwone]
    exact integrableOn_const hVfin.ne
  have hbound : ∀ n ≤ T,
      IntegrableOn (ewooWeight α ℓ (n+1)) V ∧
      (∫ x in V, ewooWeight α ℓ (n+1) x) ≤
        (volume V).toReal * Real.exp (-α * ∑ t ∈ Finset.Icc 1 n, ℓ t (ewooPoint V α ℓ t)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨hbase,?_⟩
      simp [ewooWeight,measureReal_def]
    | succ n ih =>
      intro hn
      obtain ⟨_,hb⟩ := ih (by omega)
      obtain ⟨_,hi,hj⟩ := hJ (n+1) (Finset.mem_Icc.mpr ⟨by omega,hn⟩)
      refine ⟨hi,?_⟩
      calc
        _ ≤ (∫ x in V, ewooWeight α ℓ (n+1) x) *
            Real.exp (-α * ℓ (n+1) (ewooPoint V α ℓ (n+1))) := hj
        _ ≤ ((volume V).toReal * Real.exp (-α * ∑ t ∈ Finset.Icc 1 n, ℓ t (ewooPoint V α ℓ t))) *
            Real.exp (-α * ℓ (n+1) (ewooPoint V α ℓ (n+1))) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = _ := by
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
          simp only [mul_add,Real.exp_add,mul_assoc]
  exact hbound T le_rfl

-- Previously accepted contribution by this account (06d5d370-ab38-49ad-a336-0eb0e241e191).
private theorem restricted_prior_complete {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : Convex ℝ V)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V)
    (α : ℝ) (hα : 0 < α)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓ : ∀ t ∈ Finset.Icc 1 T, ExpConcaveOn V α (ℓ t)) :
    ∀ x ∈ shrunkSet V u T, ∃ w ∈ V,
      x = (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) • u +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) • w ∧
      (∀ t ∈ Finset.Icc 1 T,
        Real.exp (-α * ℓ t x) ≥
          (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u) +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) * Real.exp (-α * ℓ t w) ∧
        (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u) +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) * Real.exp (-α * ℓ t w) ≥
          (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u)) ∧
      Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t x) ≥
        ((((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) ^ T) *
        Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) ∧
      Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t x) ≥
        Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) / Real.exp (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  let r : ℝ := ((T : ℝ) / d) / ((T : ℝ) / d + 1)
  let s : ℝ := 1 / ((T : ℝ) / d + 1)
  have hden : 0 < (T : ℝ) / d + 1 := by positivity
  have hr : 0 < r := div_pos (div_pos hTR hdR) hden
  have hs : 0 < s := div_pos zero_lt_one hden
  have hrs : r + s = 1 := by dsimp [r, s]; field_simp
  intro x hx
  obtain ⟨w, hw, hwx⟩ := hx
  have hxrep : x = r • u + s • w := hwx.symm
  have hround : ∀ t ∈ Finset.Icc 1 T,
      r * Real.exp (-α * ℓ t u) + s * Real.exp (-α * ℓ t w) ≤ Real.exp (-α * ℓ t x) ∧
      r * Real.exp (-α * ℓ t u) ≤ r * Real.exp (-α * ℓ t u) + s * Real.exp (-α * ℓ t w) := by
    intro t ht
    constructor
    · rw [hxrep]
      exact (hℓ t ht).2 hu hw hr.le hs.le hrs
    · linarith [mul_pos hs (Real.exp_pos (-α * ℓ t w))]
  have hpoint : ∀ t ∈ Finset.Icc 1 T,
      Real.log r + -α * ℓ t u ≤ -α * ℓ t x := by
    intro t ht
    have h := Real.log_le_log (mul_pos hr (Real.exp_pos _)) ((hround t ht).2.trans (hround t ht).1)
    simpa only [Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp] using h
  have hsum : (T : ℝ) * Real.log r + -α * ∑ t ∈ Finset.Icc 1 T, ℓ t u ≤
      -α * ∑ t ∈ Finset.Icc 1 T, ℓ t x := by
    have h := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] using h
  have hexp := Real.exp_le_exp.mpr hsum
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hr] at hexp
  have hlog : -(d : ℝ) ≤ (T : ℝ) * Real.log r := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hr) hTR.le
    have heq : (T : ℝ) * (1 - r⁻¹) = -(d : ℝ) := by
      dsimp [r]
      field_simp
      ring
    rwa [heq] at h
  refine ⟨w, hw, hxrep, hround, hexp, ?_⟩
  have hlast := Real.exp_le_exp.mpr (add_le_add_right hlog (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u))
  rw [Real.exp_add, Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log hr] at hlast
  change Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) / Real.exp (d : ℝ) ≤ _
  calc
    _ = (Real.exp (d : ℝ))⁻¹ * Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) := by ring
    _ ≤ r ^ T * Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) := by simpa [mul_comm] using hlast
    _ ≤ _ := hexp



-- Reused with attribution: vebis, accepted submission 47273ee3-bd32-4c72-97de-ae5b465c5d55.
private theorem shrunk_volume_complete {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ V) (hclosed : IsClosed V) (hbounded : Bornology.IsBounded V)
    (hvol_pos : 0 < volume V) (hvol_fin : volume V < ⊤)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) :
    volume (shrunkSet V u T) / volume V =
      ENNReal.ofReal (1 / (((T : ℝ) / (d : ℝ) + 1) ^ d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  set t : ℝ := 1 / ((T : ℝ) / (d : ℝ) + 1) with ht
  have hpos : 0 < (T : ℝ) / (d : ℝ) + 1 := by positivity
  have hset : shrunkSet V u T = AffineMap.homothety u t '' V := by
    unfold shrunkSet
    congr 1
    funext w
    have hc : ((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1) = 1 - t := by
      rw [ht]; field_simp; ring
    rw [hc, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rw [hset, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    ENNReal.mul_div_cancel_right hvol_pos.ne' hvol_fin.ne]
  congr 1
  rw [abs_of_pos (by positivity), ht, one_div, inv_pow, one_div]

theorem solution {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ V) (hclosed : IsClosed V) (hbounded : Bornology.IsBounded V)
    (hvol_pos : 0 < volume V)
    (α : ℝ) (hα : 0 < α)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hexp : ∀ t ∈ Finset.Icc 1 T, ExpConcaveOn V α (ℓ t))
    (hmeas : ∀ t ∈ Finset.Icc 1 T, AEMeasurable (ℓ t) (volume.restrict V))
    (hint_weight : ∀ t ∈ Finset.Icc 1 T, IntegrableOn (ewooWeight α ℓ t) V)
    (hint_point : ∀ t ∈ Finset.Icc 1 T, IntegrableOn (fun x => ewooWeight α ℓ t x • x) V) :
    ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (ewooPoint V α ℓ t) - ℓ t u)) ≤
        (d : ℝ) / α * (1 + Real.log ((T : ℝ) / (d : ℝ) + 1)) := by
  intro u hu
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  let D : ℝ := (T : ℝ) / d + 1
  let r : ℝ := ((T : ℝ) / d) / D
  let s : ℝ := 1 / D
  have hD : 0 < D := by dsimp [D];positivity
  have hr : 0 < r := by dsimp [r];positivity
  have hs : 0 < s := by dsimp [s];positivity
  have hrs : r+s=1 := by dsimp [r,s,D];field_simp
  let S := shrunkSet V u T
  have hSsub : S ⊆ V := by
    rintro x ⟨w,hw,rfl⟩
    exact hconv hu hw hr.le hs.le hrs
  have hcompact : IsCompact V := isCompact_iff_isClosed_bounded.mpr ⟨hclosed,hbounded⟩
  have hScompact : IsCompact S := hcompact.image
    ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => r • u)).add
      (continuous_const_smul s))
  have hSmeas : MeasurableSet S := hScompact.measurableSet
  have hVfin : volume V < ∞ := hbounded.measure_lt_top
  have hVreal : 0 < (volume V).toReal := ENNReal.toReal_pos hvol_pos.ne' hVfin.ne
  have hratio : (volume S).toReal / (volume V).toReal = 1 / D^d := by
    have he := shrunk_volume_complete hd T hT V hconv hclosed hbounded hvol_pos hVfin u hu
    change volume S / volume V = ENNReal.ofReal (1 / D^d) at he
    have hre := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / D^d)] using hre
  obtain ⟨hweight,hupper⟩ := waa_partition_upper T V hconv hclosed hbounded hvol_pos α ℓ
    hexp hmeas hint_weight hint_point
  let A := Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) / Real.exp (d : ℝ)
  have hA : 0 < A := by dsimp [A];positivity
  have hpoint : ∀ x ∈ S, A ≤ ewooWeight α ℓ (T+1) x := by
    intro x hx
    obtain ⟨w,hw,he,hround,hprod,hfinal⟩ :=
      restricted_prior_complete hd T hT V hconv u hu α hα ℓ hexp x hx
    simpa only [ewooWeight,Finset.Ico_add_one_right_eq_Icc] using hfinal
  have hlow : (volume S).toReal * A ≤ ∫ x in V, ewooWeight α ℓ (T+1) x := by
    calc
      _ = ∫ _x in S, A := by simp [setIntegral_const,measureReal_def]
      _ ≤ ∫ x in S, ewooWeight α ℓ (T+1) x :=
        setIntegral_mono_on (integrableOn_const hScompact.measure_lt_top.ne)
          (hweight.mono_set hSsub) hSmeas hpoint
      _ ≤ _ := setIntegral_mono_set hweight
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
        (Filter.Eventually.of_forall (fun _ hx => hSsub hx))
  have hnorm : (1/D^d)*A ≤ Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t (ewooPoint V α ℓ t)) := by
    rw [← hratio]
    calc
      _ = ((volume S).toReal * A) / (volume V).toReal := by ring
      _ ≤ ((volume V).toReal * Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t (ewooPoint V α ℓ t))) /
          (volume V).toReal := div_le_div_of_nonneg_right (hlow.trans hupper) hVreal.le
      _ = _ := by field_simp
  have hp : 0 < (1/D^d)*A := by positivity
  have hlog := Real.log_le_log hp hnorm
  rw [Real.log_mul (by positivity : (1/D^d) ≠ 0) hA.ne',
    Real.log_div one_ne_zero (pow_pos hD d).ne',Real.log_one,Real.log_pow,
    Real.log_exp] at hlog
  have hlogA : Real.log A = -α * ∑ t ∈ Finset.Icc 1 T, ℓ t u - (d : ℝ) := by
    dsimp [A]
    rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp,Real.log_exp]
  rw [hlogA] at hlog
  rw [Finset.sum_sub_distrib]
  have he : (d : ℝ) / α * (1 + Real.log D) = ((d : ℝ) * (1+Real.log D))/α := by ring
  change _ ≤ (d : ℝ) / α * (1 + Real.log D)
  rw [he]
  apply (le_div_iff₀ hα).mpr
  nlinarith

