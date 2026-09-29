-- Prove2me | solution 1 for NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b1926604-cbf4-5879-833d-1fe7e21e6564

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

import Theorems.Thm_Valued_finite_image_v_of_isCompact_of_zero_notMem
import Theorems.Thm_Subgroup_existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem
import Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
import Theorems.Thm_NumberField_Idele_exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
import Theorems.Thm_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn
import Theorems.Thm_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord
import Theorems.Thm_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
import Theorems.Thm_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen
import Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units
import Theorems.Thm_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
import Theorems.Thm_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
import Theorems.Thm_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
import Theorems.Thm_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
import Theorems.Thm_Real_abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff
import Theorems.Thm_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
import Theorems.Thm_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
import Theorems.Thm_NumberField_Idele_exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
import Theorems.Thm_NumberField_mixedEmbedding_exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord
import Theorems.Thm_Subgroup_sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace NumCore

theorem ord_unitsMap (K : Type) [Field K] [NumberField K] (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
      -Multiplicative.toAdd (v.valuationOfNeZero u) := by
  unfold NumberField.Idele.ord
  have h1 : (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((u : K) : v.adicCompletion K) := rfl
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    ← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  rfl

theorem emb_eq (K : Type) [Field K] [NumberField K] (u : K) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) u)) =
      NumberField.mixedEmbedding K u := by
  rw [NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, AdelicLevel.adeleArch_apply]
  rfl

theorem snd_unitsMap_apply (K : Type) [Field K] [NumberField K] (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((u : K) : v.adicCompletion K) := rfl

theorem finsum_mem_ite {α M : Type*} [AddCommMonoid M] (s : Set α) (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∑ᶠ a ∈ s, (if p a then f a else 0) = ∑ᶠ a ∈ s ∩ {a | p a}, f a := by
  rw [finsum_mem_def, finsum_mem_def]
  congr 1
  funext a
  by_cases ha : a ∈ s <;> by_cases hp : p a <;>
    simp [ha, hp]

end NumCore

namespace NumCore

open NumberField NumberField.InfinitePlace in
theorem continuous_ringEquiv_mixedSpace (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have h : (fun x : InfiniteAdeleRing K => InfiniteAdeleRing.ringEquiv_mixedSpace K x) =
      fun x => ((fun (v : {w : InfinitePlace K // IsReal w}) => Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun (v : {w : InfinitePlace K // IsComplex w}) => Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  show Continuous fun x : InfiniteAdeleRing K => InfiniteAdeleRing.ringEquiv_mixedSpace K x
  rw [h]
  exact (continuous_pi fun v => (Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
    (continuous_pi fun v => (Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1))

theorem algebraMap_adicCompletion_apply (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    algebraMap K (v.adicCompletion K) x = (x : v.adicCompletion K) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

end NumCore

namespace NumCore

theorem norm_sub_one_mul_inv_kink {F : Type*} [NormedField F] (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ‖x - 1‖ * (‖1 - x⁻¹‖ / Real.sqrt ‖x⁻¹‖)⁻¹ = Real.sqrt ‖x‖ := by
  have h1 : 1 - x⁻¹ = x⁻¹ * (x - 1) := by field_simp
  have hn : ‖x - 1‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact sub_ne_zero.2 hx1
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  rw [h1, norm_mul, norm_inv, Real.sqrt_inv]
  have hs : Real.sqrt ‖x‖ ≠ 0 := (Real.sqrt_pos.2 hxn).ne'
  have hsq : Real.sqrt ‖x‖ * Real.sqrt ‖x‖ = ‖x‖ := Real.mul_self_sqrt hxn.le
  field_simp
  nlinarith [hsq, hs, hn, hxn]

theorem arch_kink_ratio (K : Type) [Field K] [NumberField K] (u : Kˣ) (hu : (u : K) ≠ 1) :
    (((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) *
      ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) -
          AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ /
          Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K
            (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ =
    (((∏ w : InfinitePlace K, (Real.sqrt ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w‖) ^ w.mult : ℝ)) : ℂ) := by
  have hcomp : ∀ (x : K) (w : InfinitePlace K),
      AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) x) w = algebraMap K w.Completion x := fun x w => rfl
  have hev : ∀ (w : InfinitePlace K) (y : InfiniteAdeleRing K), NumberField.AdelicLevel.archEval K w y = y w := fun w y => rfl
  have hsub : ∀ (y y' : InfiniteAdeleRing K) (w : InfinitePlace K), (y - y') w = y w - y' w := fun _ _ _ => rfl
  have hone : ∀ w : InfinitePlace K, (1 : InfiniteAdeleRing K) w = 1 := fun _ => rfl
  simp only [hev, hsub, hone, hcomp, Units.val_inv_eq_inv_val, map_inv₀]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hx0 : algebraMap K w.Completion (u : K) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap K w.Completion).injective]; exact u.ne_zero
  have hx1 : algebraMap K w.Completion (u : K) ≠ 1 := by
    rw [Ne, ← (algebraMap K w.Completion).map_one, (algebraMap K w.Completion).injective.eq_iff]; exact hu
  rw [← inv_pow, ← mul_pow, NumCore.norm_sub_one_mul_inv_kink _ hx0 hx1]

theorem local_kink_ratio (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a t : (v.adicCompletion K)ˣ) (ht1 : (t : v.adicCompletion K) ≠ 1) :
    ((‖((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ : ℝ) : ℂ) *
      ((((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) *
          AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ)) : ℂ))⁻¹ =
      ((Real.sqrt ‖((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℝ) : ℂ) := by
  have hr : AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) =
      ‖1 - (((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))⁻¹‖ := by
    simp only [AutomorphicForm.LocalWeightedOrbital.ratio, Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]
    congr 1
    field_simp
  have hs : AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) =
      (Real.sqrt ‖(((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))⁻¹‖)⁻¹ := by
    simp only [AutomorphicForm.LocalWeightedOrbital.sqrtRatio, Units.val_mul, Units.val_inv_eq_inv_val, inv_inv, norm_mul]
    rw [← Real.sqrt_inv]
    congr 1
    have : ‖(a : v.adicCompletion K)‖ ≠ 0 := norm_ne_zero_iff.2 a.ne_zero
    field_simp
  rw [hr, hs, ← div_eq_mul_inv ‖1 - _‖, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  have h0 : (((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ≠ 0 := (t⁻¹).ne_zero
  have h1 : (((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ≠ 1 := by
    rw [Units.val_inv_eq_inv_val]; exact fun h => ht1 (inv_eq_one.1 h)
  exact NumCore.norm_sub_one_mul_inv_kink _ h0 h1

open Filter Topology in

theorem zeroExt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ Φf : (v.adicCompletion K) × (v.adicCompletion K) → ℂ,
      IsLocallyConstant Φf ∧ HasCompactSupport Φf ∧ (∀ p, Φf p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
      ∀ u z : (v.adicCompletion K)ˣ, Φf ((u : v.adicCompletion K), (z : v.adicCompletion K)) = Φ (u, z) := by
  classical
  set Kv := v.adicCompletion K
  let ι : Kvˣ × Kvˣ → Kv × Kv := fun q => ((q.1 : Kv), (q.2 : Kv))
  have hι : Continuous ι := Units.continuous_val.prodMap Units.continuous_val
  have hιinj : Function.Injective ι := fun a b h => by
    simp only [ι, Prod.mk.injEq] at h
    exact Prod.ext (Units.ext h.1) (Units.ext h.2)
  let Φf : Kv × Kv → ℂ := fun p => if h : IsUnit p.1 ∧ IsUnit p.2 then Φ (h.1.unit, h.2.unit) else 0
  have hval : ∀ u z : Kvˣ, Φf ((u : Kv), (z : Kv)) = Φ (u, z) := by
    intro u z
    have h : IsUnit (u : Kv) ∧ IsUnit (z : Kv) := ⟨u.isUnit, z.isUnit⟩
    simp only [Φf, dif_pos h]
    congr 1
    ext <;> simp [IsUnit.unit_spec]
  have hΦfι : ∀ q, Φf (ι q) = Φ q := fun q => hval q.1 q.2

  set Kc : Set (Kv × Kv) := ι '' tsupport Φ
  have hKc : IsCompact Kc := hcs.image hι
  have hzero : ∀ x, x ∉ Kc → Φf x = 0 := by
    intro x hx
    by_cases h : IsUnit x.1 ∧ IsUnit x.2
    · have hx' : x = ι (h.1.unit, h.2.unit) := by
        simp [ι, IsUnit.unit_spec]
      rw [hx', hΦfι]
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hx (hx' ▸ Set.mem_image_of_mem ι hmem)
    · simp only [Φf, dif_neg h]
  refine ⟨Φf, ?_, HasCompactSupport.intro hKc hzero, ?_, hval⟩
  ·
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ Kc
    · obtain ⟨q, hq, rfl⟩ := hx
      have hvalemb : IsOpenEmbedding (Units.val : Kvˣ → Kv) := by
        refine ⟨Units.isEmbedding_val₀, ?_⟩
        have hr : Set.range (Units.val : Kvˣ → Kv) = {x | x ≠ 0} := by
          ext x
          simp only [Set.mem_range, Set.mem_setOf_eq]
          exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
        rw [hr]
        exact isOpen_ne
      have hopen : IsOpenEmbedding ι := hvalemb.prodMap hvalemb
      have h1 : ∀ᶠ q' in nhds q, Φ q' = Φ q := (IsLocallyConstant.iff_eventually_eq Φ).1 hlc q
      rw [← hopen.map_nhds_eq q, Filter.eventually_map]
      filter_upwards [h1] with q' hq'
      rw [hΦfι, hΦfι, hq']
    · have : ∀ᶠ y in nhds x, y ∉ Kc := hKc.isClosed.isOpen_compl.mem_nhds hx
      filter_upwards [this] with y hy
      rw [hzero y hy, hzero x hx]
  · intro p hp
    by_cases h : IsUnit p.1 ∧ IsUnit p.2
    · exact ⟨h.1.ne_zero, h.2.ne_zero⟩
    · simp [Φf, dif_neg h] at hp

end NumCore

section NumdDefectHelpers

open scoped Classical

namespace NumdDefect

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def twistHomeo : G × G ≃ₜ G × G where
  toFun p := (p.2 * p.1, p.1⁻¹)
  invFun p := (p.2⁻¹, p.1 * p.2)
  left_inv p := by
    obtain ⟨b, z⟩ := p
    simp only [inv_inv, Prod.mk.injEq, true_and]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  right_inv p := by
    obtain ⟨a, t⟩ := p
    simp only [inv_inv, Prod.mk.injEq, and_true]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  continuous_toFun := (continuous_snd.mul continuous_fst).prodMk continuous_fst.inv
  continuous_invFun := continuous_snd.inv.prodMk (continuous_fst.mul continuous_snd)

theorem twistHomeo_apply (p : G × G) : (twistHomeo (G := G)) p = (p.2 * p.1, p.1⁻¹) := rfl

theorem isLocallyConstant_hasCompactSupport_comp_twist (Ψ₀ : G × G → ℂ)
    (hlc : IsLocallyConstant Ψ₀) (hcs : HasCompactSupport Ψ₀) :
    IsLocallyConstant (fun p : G × G => Ψ₀ (p.2 * p.1, p.1⁻¹)) ∧
      HasCompactSupport (fun p : G × G => Ψ₀ (p.2 * p.1, p.1⁻¹)) := by
  have heq : (fun p : G × G => Ψ₀ (p.2 * p.1, p.1⁻¹)) = Ψ₀ ∘ (twistHomeo (G := G)) := rfl
  rw [heq]
  exact ⟨fun s => by rw [Set.preimage_comp]; exact (hlc s).preimage (twistHomeo (G := G)).continuous,
    hcs.comp_homeomorph _⟩

theorem cellIndicator_isLocallyConstant_hasCompactSupport_invariant
    (A V : Subgroup G) (hAo : IsOpen (A : Set G)) (hAc : IsCompact (A : Set G)) (hVo : IsOpen (V : Set G))
    (hVA : V ≤ A) (α τ : G) :
    let I : G × G → ℂ := fun p => if (p.2 * p.1)⁻¹ * α ∈ A ∧ p.1 * τ ∈ V then 1 else 0
    IsLocallyConstant I ∧ HasCompactSupport I ∧ ∀ (b z σ : G), σ ∈ V → I (b * σ, z) = I (b, z) := by
  classical
  intro I

  set S : Set (G × G) := {p | (p.2 * p.1)⁻¹ * α ∈ A ∧ p.1 * τ ∈ V} with hS
  have hcont1 : Continuous fun p : G × G => (p.2 * p.1)⁻¹ * α := ((continuous_snd.mul continuous_fst).inv).mul continuous_const
  have hcont2 : Continuous fun p : G × G => p.1 * τ := continuous_fst.mul continuous_const
  have hAcl : IsClosed (A : Set G) := A.isClosed_of_isOpen hAo
  have hVcl : IsClosed (V : Set G) := V.isClosed_of_isOpen hVo
  have hSo : IsOpen S := (hAo.preimage hcont1).inter (hVo.preimage hcont2)
  have hScl : IsClosed S := (hAcl.preimage hcont1).inter (hVcl.preimage hcont2)
  have hI : ∀ p, I p = if p ∈ S then 1 else 0 := fun p => by simp only [I, hS, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    by_cases hp : p ∈ S
    · exact Filter.eventually_of_mem (hSo.mem_nhds hp) fun q hq => by rw [hI, hI, if_pos hq, if_pos hp]
    · exact Filter.eventually_of_mem (hScl.isOpen_compl.mem_nhds hp) fun q hq => by
        rw [hI, hI, if_neg (show q ∉ S from hq), if_neg hp]
  ·
    have hVc : IsCompact (V : Set G) := hAc.of_isClosed_subset hVcl (fun x hx => hVA hx)
    set C₁ : Set G := (fun σ : G => σ * τ⁻¹) '' (V : Set G) with hC₁
    set C₂ : Set G := (fun q : G × G => α * q.1 * τ * q.2⁻¹) '' ((A : Set G) ×ˢ (V : Set G)) with hC₂
    have hC₁c : IsCompact C₁ := hVc.image (continuous_id.mul continuous_const)
    have hC₂c : IsCompact C₂ := (hAc.prod hVc).image
      (((continuous_const.mul continuous_fst).mul continuous_const).mul continuous_snd.inv)
    refine HasCompactSupport.intro (hC₁c.prod hC₂c) fun p hp => ?_
    rw [hI, if_neg]
    intro hpS
    apply hp
    obtain ⟨h1, h2⟩ := hpS
    refine ⟨⟨p.1 * τ, h2, by show p.1 * τ * τ⁻¹ = p.1; rw [mul_inv_cancel_right]⟩, ⟨(α⁻¹ * (p.2 * p.1), p.1 * τ), ⟨?_, h2⟩, ?_⟩⟩
    · have := A.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at this
    · show α * (α⁻¹ * (p.2 * p.1)) * τ * (p.1 * τ)⁻¹ = p.2
      rw [mul_inv_cancel_left, mul_inv_rev, mul_assoc (p.2 * p.1) τ, mul_inv_cancel_left, mul_inv_cancel_right]
  · intro b z σ hσ
    have hσA : σ ∈ A := hVA hσ
    have hiff : (b * σ, z) ∈ S ↔ (b, z) ∈ S := by
      show ((z * (b * σ))⁻¹ * α ∈ A ∧ b * σ * τ ∈ V) ↔ ((z * b)⁻¹ * α ∈ A ∧ b * τ ∈ V)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have : (z * b)⁻¹ * α = σ * ((z * (b * σ))⁻¹ * α) := by group
          rw [this]; exact A.mul_mem hσA h1
        · have : b * τ = (b * σ * τ) * σ⁻¹ := by rw [mul_right_comm b σ τ, mul_inv_cancel_right]
          rw [this]; exact V.mul_mem h2 (V.inv_mem hσ)
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have : (z * (b * σ))⁻¹ * α = σ⁻¹ * ((z * b)⁻¹ * α) := by group
          rw [this]; exact A.mul_mem (A.inv_mem hσA) h1
        · have : b * σ * τ = (b * τ) * σ := mul_right_comm b σ τ
          rw [this]; exact V.mul_mem h2 hσ
    rw [hI, hI]
    by_cases h : (b, z) ∈ S
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

end NumdDefect

end NumdDefectHelpers

section PccSmoothHelpers

set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

namespace PccSmooth

variable (K : Type) [Field K] [NumberField K]

theorem isOpen_isUnit : IsOpen {y : mixedSpace K | IsUnit y} := Units.isOpen

theorem fst_ne_zero_of_isUnit {y : mixedSpace K} (hy : IsUnit y) (i : {w : InfinitePlace K // IsReal w}) : y.1 i ≠ 0 :=
  ((hy.map (RingHom.fst _ _)).map (Pi.evalRingHom _ i)).ne_zero

theorem snd_ne_zero_of_isUnit {y : mixedSpace K} (hy : IsUnit y) (i : {w : InfinitePlace K // IsComplex w}) : y.2 i ≠ 0 :=
  ((hy.map (RingHom.snd _ _)).map (Pi.evalRingHom _ i)).ne_zero

theorem normAtPlace_pos_of_isUnit (w : InfinitePlace K) {y : mixedSpace K} (hy : IsUnit y) : 0 < normAtPlace w y := by
  by_cases hw : IsReal w
  · rw [normAtPlace_apply_of_isReal hw]; exact norm_pos_iff.2 (fst_ne_zero_of_isUnit K hy ⟨w, hw⟩)
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
    exact norm_pos_iff.2 (snd_ne_zero_of_isUnit K hy ⟨w, _⟩)

theorem contDiffAt_normAtPlace {n : WithTop ℕ∞} (w : InfinitePlace K) {y : mixedSpace K} (hy : IsUnit y) :
    ContDiffAt ℝ n (fun y : mixedSpace K => normAtPlace w y) y := by
  by_cases hw : IsReal w
  · have h : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.1 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isReal hw y
    rw [h]
    have h1 : ContDiffAt ℝ n (fun y : mixedSpace K => y.1 ⟨w, hw⟩) y :=
      ((contDiffAt_apply ℝ ℝ (⟨w, hw⟩ : {w : InfinitePlace K // IsReal w}) y.1).comp y contDiffAt_fst)
    exact (contDiffAt_norm ℝ (fst_ne_zero_of_isUnit K hy ⟨w, hw⟩)).comp y h1
  · have hw' : IsComplex w := not_isReal_iff_isComplex.mp hw
    have h : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.2 ⟨w, hw'⟩‖ :=
      funext fun y => normAtPlace_apply_of_isComplex hw' y
    rw [h]
    have h1 : ContDiffAt ℝ n (fun y : mixedSpace K => y.2 ⟨w, hw'⟩) y :=
      ((contDiffAt_apply ℝ ℂ (⟨w, hw'⟩ : {w : InfinitePlace K // IsComplex w}) y.2).comp y contDiffAt_snd)
    exact (contDiffAt_norm ℝ (snd_ne_zero_of_isUnit K hy ⟨w, hw'⟩)).comp y h1

theorem contDiffOn_normAtPlace_rpow {n : WithTop ℕ∞} (w : InfinitePlace K) (r : ℝ) :
    ContDiffOn ℝ n (fun y : mixedSpace K => (normAtPlace w y) ^ r) {y : mixedSpace K | IsUnit y} := by
  intro y hy
  have hy' : IsUnit y := hy
  exact ((Real.contDiffAt_rpow_const_of_ne (p := r) (normAtPlace_pos_of_isUnit K w hy').ne').comp y
    (contDiffAt_normAtPlace K w hy')).contDiffWithinAt

theorem contDiffOn_log_normAtPlace {n : WithTop ℕ∞} (w : InfinitePlace K) :
    ContDiffOn ℝ n (fun y : mixedSpace K => Real.log (normAtPlace w y)) {y : mixedSpace K | IsUnit y} := by
  intro y hy
  have hy' : IsUnit y := hy
  exact ((Real.contDiffAt_log.2 (normAtPlace_pos_of_isUnit K w hy').ne').comp y
    (contDiffAt_normAtPlace K w hy')).contDiffWithinAt

theorem contDiff_norm_one_sub_sq {n : WithTop ℕ∞} (w : {w : InfinitePlace K // IsComplex w}) :
    ContDiff ℝ n (fun y : mixedSpace K => ‖(1 : ℂ) - y.2 w‖ ^ 2) := by
  have h1 : ContDiff ℝ n (fun y : mixedSpace K => (1 : ℂ) - y.2 w) :=
    contDiff_const.sub ((contDiff_apply ℝ ℂ w).comp contDiff_snd)
  exact (contDiff_norm_sq ℝ).comp h1

theorem contDiff_one_sub_sq_real {n : WithTop ℕ∞} (w : {w : InfinitePlace K // IsReal w}) :
    ContDiff ℝ n (fun y : mixedSpace K => ((1 : ℝ) - y.1 w) ^ 2) :=
  (contDiff_const.sub ((contDiff_apply ℝ ℝ w).comp contDiff_fst)).pow 2

theorem contDiff_mul_of_contDiffOn_isUnit
    (W : mixedSpace K → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y) (hW0 : ∀ y, W y ≠ 0 → y ∈ C₀)
    (g : mixedSpace K → ℂ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {y : mixedSpace K | IsUnit y}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => g y * W y) ∧
      (∀ y : mixedSpace K, g y * W y ≠ 0 → y ∈ C₀) ∧ HasCompactSupport (fun y : mixedSpace K => g y * W y) := by
  have hsupp : ∀ y : mixedSpace K, g y * W y ≠ 0 → y ∈ C₀ := fun y hy => hW0 y (right_ne_zero_of_mul hy)
  refine ⟨?_, hsupp, HasCompactSupport.intro hC₀ fun y hy => by_contra fun h => hy (hsupp y h)⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : IsUnit y
  · exact (hg.contDiffAt ((isOpen_isUnit K).mem_nhds hy)).mul hW.contDiffAt
  · have hyC : y ∉ C₀ := fun h => hy (hC₀u y h)
    have hev : (fun y : mixedSpace K => g y * W y) =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hC₀.isClosed.isOpen_compl.mem_nhds hyC] with y' hy'
      by_contra h
      exact hy' (hsupp y' h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem contDiff_ofReal_mul_of_contDiffOn_isUnit
    (W : mixedSpace K → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y) (hW0 : ∀ y, W y ≠ 0 → y ∈ C₀)
    (g : mixedSpace K → ℝ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {y : mixedSpace K | IsUnit y}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => ((g y : ℝ) : ℂ) * W y) ∧
      (∀ y : mixedSpace K, ((g y : ℝ) : ℂ) * W y ≠ 0 → y ∈ C₀) ∧
      HasCompactSupport (fun y : mixedSpace K => ((g y : ℝ) : ℂ) * W y) :=
  contDiff_mul_of_contDiffOn_isUnit K W hW C₀ hC₀ hC₀u hW0 (fun y => ((g y : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hg)

end PccSmooth

end PccSmoothHelpers

section PccKinkHelpers

set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain
open scoped Classical

namespace PccKink

variable (K : Type) [Field K] [NumberField K]

theorem norm_algebraMap_completion (w : InfinitePlace K) (x : K) : ‖algebraMap K w.Completion x‖ = w x := by
  show ‖(((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion)‖ = w x
  rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply]

theorem kinkScalar_eq (w : InfinitePlace K) (u : Kˣ) :
    ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ = w (1 - ((u⁻¹ : Kˣ) : K)) := by
  have h : NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) -
      AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))) =
      algebraMap K w.Completion (1 - ((u⁻¹ : Kˣ) : K)) := by
    rw [map_sub (algebraMap K w.Completion), map_one (algebraMap K w.Completion), map_sub, map_one]; rfl
  rw [h, norm_algebraMap_completion]

theorem norm_adeleArch_algebraMap_eq_normAtPlace (w : InfinitePlace K) (u : Kˣ) :
    ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w‖ = normAtPlace w (mixedEmbedding K (u : K)) := by
  rw [normAtPlace_apply]
  exact norm_algebraMap_completion K w (u : K)

theorem isUnit_mixedEmbedding (u : Kˣ) : IsUnit (mixedEmbedding K (u : K)) := u.isUnit.map _

variable
  (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
        (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
  (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
  (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
  (hP_inv : ∀ y : mixedSpace K, IsUnit y →
      P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
          Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y)
  (hP_fst : ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
      (w : {w : InfinitePlace K // w.IsReal}),
      (P s (x, θ)).1 w = (((s w : ℤˣ) : ℤ) : ℝ) * Real.exp (x (Fintype.equivFin (InfinitePlace K) w.1)))
  (hP_snd : ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
      (w : {w : InfinitePlace K // w.IsComplex}),
      (P s (x, θ)).2 w = Complex.exp (((x (Fintype.equivFin (InfinitePlace K) w.1) / 2 : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * ((θ (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) : ℂ)))

include hP_inv hP_fst in

theorem embedding_of_isReal_eq (u : Kˣ) (w : InfinitePlace K) (hw : w.IsReal) :
    embedding_of_isReal hw (u : K) =
      (((sgn (mixedEmbedding K (u : K)) ⟨w, hw⟩ : ℤˣ) : ℤ) : ℝ) * Real.exp ((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w)) := by
  have h := congrArg (fun y : mixedSpace K => y.1 ⟨w, hw⟩) (hP_inv _ (isUnit_mixedEmbedding K u))
  rw [hP_fst, mixedEmbedding_apply_isReal] at h
  exact h.symm

include hP_inv hP_snd in

theorem embedding_eq (u : Kˣ) (w : InfinitePlace K) (hw : w.IsComplex) :
    w.embedding (u : K) =
      Complex.exp ((((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * ((arg (mixedEmbedding K (u : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ)) := by
  have h := congrArg (fun y : mixedSpace K => y.2 ⟨w, hw⟩) (hP_inv _ (isUnit_mixedEmbedding K u))
  rw [hP_snd, mixedEmbedding_apply_isComplex] at h
  exact h.symm

include hP_inv hP_fst in

theorem kinkScalar_real (u : Kˣ) (w : InfinitePlace K) (hw : w.IsReal) :
    ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
      if sgn (mixedEmbedding K (u : K)) ⟨w, hw⟩ = 1
      then Real.exp (-((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w))) * |1 - Real.exp ((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w))|
      else 1 + Real.exp (-((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w))) := by
  obtain ⟨hR1, hR2, -, -⟩ := Real.abs_one_sub_exp_inv_eq_exp_neg_mul_abs_one_sub_exp_and_contDiff
  rw [kinkScalar_eq, ← norm_embedding_of_isReal hw, map_sub, map_one, Units.val_inv_eq_inv_val, map_inv₀,
    embedding_of_isReal_eq K P sgn arg hP_inv hP_fst u w hw, Real.norm_eq_abs]
  rcases Int.units_eq_one_or (sgn (mixedEmbedding K (u : K)) ⟨w, hw⟩) with hs | hs
  · rw [if_pos hs, hs, Units.val_one, Int.cast_one, one_mul, hR1]
  · have hne : sgn (mixedEmbedding K (u : K)) ⟨w, hw⟩ ≠ 1 := by rw [hs]; decide
    rw [if_neg hne, hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul, hR2]

include hP_inv hP_snd in

theorem kinkScalar_complex (u : Kˣ) (w : InfinitePlace K) (hw : w.IsComplex) :
    ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
        Real.exp (-((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2)) *
          ‖(1 : ℂ) - Complex.exp ((((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * ((arg (mixedEmbedding K (u : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ ∧
      ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
        Real.exp (-((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w))) *
          (‖(1 : ℂ) - Complex.exp ((((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((arg (mixedEmbedding K (u : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((arg (mixedEmbedding K (u : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ -
          (fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 *
            ‖(1 : ℂ) - Complex.exp ((((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((arg (mixedEmbedding K (u : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2) := by
  obtain ⟨hC1, hC2, -, -⟩ := Complex.norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff
  have hk : ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
      ‖(1 : ℂ) - (Complex.exp ((((fun i : Fin (Fintype.card (InfinitePlace K)) => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) * Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) (mixedEmbedding K (u : K)))) (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * ((arg (mixedEmbedding K (u : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ)))⁻¹‖ := by
    rw [kinkScalar_eq, ← norm_embedding_eq w, map_sub, map_one, Units.val_inv_eq_inv_val, map_inv₀,
      embedding_eq K P sgn arg hP_inv hP_snd u w hw]
  rw [hk]
  exact ⟨hC1 _ _, hC2 _ _⟩

end PccKink

end PccKinkHelpers
set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]

    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK) (hT2 : 2 ≤ T.card)
    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v)
    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ f v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ f v = ζ v)

    (Φa : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hΦa_smooth : ContDiff ℝ (⊤ : ℕ∞) Φa) (hΦa_cs : HasCompactSupport Φa)
    (hΦa_units : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)))
    (Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCa : IsCompact Ca)
    (hΦa_Ca : ∀ p ∈ tsupport Φa, ∃ q ∈ Ca,
      p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
            InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)])

    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ SK, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧ ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)

    (Bd : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (Cd Ed : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hBd_smooth : ContDiff ℝ (⊤ : ℕ∞) Bd) (hCd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Cd w))
    (hEd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ed w))
    (hBd_cs : HasCompactSupport Bd) (hCd_cs : ∀ w, HasCompactSupport (Cd w)) (hEd_cs : ∀ w, HasCompactSupport (Ed w))
    (hBCE_units : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, (Bd p ≠ 0 ∨ ∃ w, Cd w p ≠ 0 ∨ Ed w p ≠ 0) →
      IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)))
    (CaD : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCaD : IsCompact CaD)
    (hBCE_Ca : ∀ p ∈ tsupport Bd ∪ ⋃ w, (tsupport (Cd w) ∪ tsupport (Ed w)),
      ∃ q ∈ CaD, p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)])

    (Ψf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ)
    (hΨf_cs : ∀ v ∈ SK, HasCompactSupport (Ψf v))
    (hΨf_lc : ∀ v ∈ SK, ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Ψf v q = Ψf v p)
    (hΨf_cells : ∀ v ∈ SK, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤
            ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
          Ψf v (a', t') = Ψf v (a, t))
    (hΨf_germ : ∀ v ∈ SK, ∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
      ‖Ψf v (a, t) - Ψf v (a, 1)‖ ≤ C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
        (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|))

    (C c' : ℂ) :
    ∃ (A q : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (kC : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → Fin (Fintype.card (NumberField.InfinitePlace K))) (kR : Fin q → Fin (Fintype.card (NumberField.InfinitePlace K)))
        (Bw : Fin A → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Cw : Fin A → Fin q → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Ew : Fin A → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ),
        (∀ a, ContDiff ℝ (⊤ : ℕ∞) (Bw a)) ∧ (∀ a k, ContDiff ℝ (⊤ : ℕ∞) (Cw a k)) ∧ (∀ a j, ContDiff ℝ (⊤ : ℕ∞) (Ew a j)) ∧
        (∀ (a : Fin A) (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          Bw a (p.1, p.2 + Pi.single j 1) = Bw a p ∧ (∀ k, Cw a k (p.1, p.2 + Pi.single j 1) = Cw a k p) ∧
            ∀ j', Ew a j' (p.1, p.2 + Pi.single j 1) = Ew a j' p) ∧
      ∃ (Sx : Set (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)), IsCompact Sx ∧
        (∀ (a : Fin A) (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), p.1 ∉ Sx → Bw a p = 0 ∧ (∀ k, Cw a k p = 0) ∧ ∀ j, Ew a j p = 0) ∧
      ∃ (sub : ℕ → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (shape : ℕ → Fin A) (lam : ℕ → ℂ), (Summable fun i => ‖lam i‖) ∧
      ∃ (x₀ : ℕ → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : ℕ → Fin T.card → ℤ) (θ₀ : ℕ → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
        C *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (f (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (c' * ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                      (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) +
              Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] *
                ∑ v ∈ SK, (((‖((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ) * ((((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) *
                        AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) : ℝ)) : ℂ))⁻¹ * Ψf v ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))), (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹))) *
                  ∏ v' ∈ SK.erase v, Φf v' (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v',
                      (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        ∑' i : ℕ, lam i * ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            Bw (shape i) (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ k : Fin q, ((|1 - Real.exp ((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kR k))| : ℝ) : ℂ) * Cw (shape i) k (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card), ((‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                    Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
                Ew (shape i) j (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by
  classical
  have hT0 : 0 < T.card := by omega
  have hr0 : 0 < Fintype.card (NumberField.InfinitePlace K) := Fintype.card_pos
  rcases Finset.eq_empty_or_nonempty Ξ with hΞ | ⟨ξ₀, hξ₀⟩
  · refine ⟨1, 0, ⊥, ?_, 0, fun _ => 1, ?_, ?_, 0, fun _ => 0, ?_, fun _ => ⟨0, hr0⟩, Fin.elim0,
      fun _ _ => 0, fun _ => Fin.elim0, fun _ _ _ => 0, ?_, ?_, ?_, ?_, ∅, isCompact_empty, ?_, fun _ => ⊥, fun _ => bot_le,
      fun _ => 0, fun _ => 0, summable_zero.congr (fun _ => by simp), fun _ => 0, fun _ => 0, fun _ => 0, fun n => ?_⟩
    · exact Subsingleton.discreteTopology
    · intro h
      have := congr_fun h ⟨0, hT0⟩
      simp at this
    · intro γ hγ
      rw [AddSubgroup.mem_bot] at hγ
      subst hγ
      simp
    · intro γ hγ j
      simp
    · intro a; exact contDiff_const
    · intro a k; exact k.elim0
    · intro a j; exact contDiff_const
    · intro a p j; exact ⟨rfl, fun k => k.elim0, fun j' => rfl⟩
    · intro a p hp; exact ⟨rfl, fun k => k.elim0, fun j => rfl⟩
    · subst hΞ
      simp

  obtain ⟨Λf, Log, hLog, hLog_mul, hΛf_mem, hΛf_disc, hΛf_pf, hΛf_ω⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul K T f hf
  obtain ⟨Λ₁, Log₁, hLog₁, hLog₁_mul, hΛ₁_mem, hΛ₁_disc, hΛ₁_pf, hΛ₁_tors⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul K T
  have hLog₁eq : ∀ u, Log₁ u = Log u := fun u => by rw [hLog, hLog₁]
  obtain ⟨F, hF_T, hF_tors, hF_dec, hF_classes⟩ :=
    NumberField.exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen K T
  obtain ⟨P, sgn, arg, hP_smooth, hP_per, hP_mul, hP_norm, hP_inv, hP_sgnarg, hP_bdd, hP_fst, hP_snd, hsgn_def, harg_def⟩ :=
    NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq K
  have hsgn1 := NumberField.mixedEmbedding.sgn_eq_one_of_forall_pos_of_polarCoord K P sgn arg
    (fun s => (hP_smooth s).continuous) hP_mul hP_norm hP_inv
  obtain ⟨ℓ, hℓ⟩ :=
    NumberField.Idele.exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
      K ξ₀ (hΞc ξ₀ hξ₀) (hΞt ξ₀ hξ₀) SK T hTS (hur ξ₀ hξ₀) f hf Nw hNwf ζ s hζ hs (fun v hv => hx ξ₀ hξ₀ v hv)

  let eflip : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) ≃+
      ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    AddEquiv.prodCongr (AddEquiv.refl _) (AddEquiv.neg _)
  let Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    Λf.map eflip.toAddMonoidHom
  have hΛ_mem : ∀ γ, γ ∈ Λ ↔ (γ.1, -γ.2) ∈ Λf := by
    intro γ
    show γ ∈ Λf.map eflip.toAddMonoidHom ↔ _
    rw [AddSubgroup.mem_map_equiv]
    rfl
  have hΛ_disc : DiscreteTopology Λ := by
    haveI := hΛf_disc
    refine DiscreteTopology.of_continuous_injective
      (f := fun y : Λ => (⟨(y.1.1, -y.1.2), (hΛ_mem _).1 y.2⟩ : Λf))
      ((continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.neg).subtype_mk _) ?_
    intro a b h
    have h' := congrArg Subtype.val h
    simp only [Prod.mk.injEq, neg_inj] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  let ω : Fin T.card → ℝ := fun j => Real.log (Nw (T.equivFin.symm j).1 : ℝ)
  have hω : ω ≠ 0 := by
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    intro h
    apply hΛf_ω hTne
    funext j
    have hj : ω j = 0 := congr_fun h j
    have hvT : (T.equivFin.symm j).1 ∈ T := (T.equivFin.symm j).2
    simp only [ω] at hj
    rw [hNwf _ hvT] at hj
    simp only [Pi.zero_apply, neg_eq_zero]
    exact_mod_cast hj
  let sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hpf : ∀ γ ∈ Λ, sl γ.1 = ∑ j, ω j * (γ.2 j : ℝ) := by
    intro γ hγ
    have hmem := (hΛ_mem γ).1 hγ
    have hR1 := hΛf_pf _ hmem
    have hsl : sl γ.1 = ∑ i, γ.1 i := by simp [sl, LinearMap.sum_apply]
    rw [hsl]
    simp only at hR1
    rw [hR1]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hvT : (T.equivFin.symm j).1 ∈ T := (T.equivFin.symm j).2
    simp only [ω, hNwf _ hvT, Pi.neg_apply, Int.cast_neg, Nat.cast_pow]
    ring

  have hLC' : ∀ v : HeightOneSpectrum (𝓞 K), ∃ U₀ : Subgroup (v.adicCompletion K)ˣ, v ∈ SK →
      (IsOpen (U₀ : Set (v.adicCompletion K)ˣ) ∧
        ∀ t ∈ U₀, ∀ b z : v.adicCompletion K, Φf v (b * (t : v.adicCompletion K), z) = Φf v (b, z)) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨U₀, h⟩ :=
        IsDedekindDomain.HeightOneSpectrum.exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
          K v (Φf v) (hΦf v hv).1 (hΦf v hv).2.1 (hΦf v hv).2.2
      exact ⟨U₀, fun _ => h⟩
    · exact ⟨⊤, fun h => absurd h hv⟩
  choose U hU using hLC'
  have hST : ∀ v ∈ SK, v ∉ T := fun v hv hvT => Finset.disjoint_left.1 hTS hvT hv
  obtain ⟨nC, cC, hcC, hclass⟩ := hF_classes (fun v => (f v : ℤ)) SK hST U (fun v hv => (hU v hv).1)

  have hΦa0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' (Prod.snd '' Ca) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hΦa_Ca p (subset_tsupport _ (Function.mem_support.2 hp))
    refine ⟨q.2, ⟨q, hq, rfl⟩, ?_⟩
    rw [hpq]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, RingEquiv.symm_apply_apply]
  have hR4 := fun (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (hξ : ξ ∈ Ξ) =>
    NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
      K νZK SK ξ (hΞc ξ hξ) Φa hΦa_smooth hΦa_cs (Prod.snd '' Ca) (hCa.image continuous_snd) hΦa0 Φf hΦf

  let A : Subgroup Kˣ :=
    { carrier := {u | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧
        ∀ v ∈ T, (f v : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u)}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun v hv => by rw [map_mul, ha1 v hv, hb1 v hv, one_mul], fun v hv => ?_⟩
        rw [map_mul, toAdd_mul]
        exact dvd_add (ha2 v hv) (hb2 v hv)
      one_mem' := ⟨fun v _ => by rw [map_one], fun v _ => by rw [map_one, toAdd_one]; exact dvd_zero _⟩
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨fun v hv => by rw [map_inv, ha1 v hv, inv_one], fun v hv => ?_⟩
        rw [map_inv, toAdd_inv]
        exact (ha2 v hv).neg_right }
  have hA_mem : ∀ u : Kˣ, u ∈ A ↔ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧
      ∀ v ∈ T, (f v : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := fun u => Iff.rfl
  let μ : Subgroup Kˣ := (NumberField.Units.torsion K).map (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K))
  have hμ_mem : ∀ z : Kˣ, z ∈ μ ↔ ∃ t : (𝓞 K)ˣ, t ∈ NumberField.Units.torsion K ∧
      Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) t = z := fun z => Subgroup.mem_map
  have hμfin : (μ : Set Kˣ).Finite := by
    rw [Subgroup.coe_map]
    haveI : Finite ((NumberField.Units.torsion K : Subgroup (𝓞 K)ˣ) : Set (𝓞 K)ˣ) :=
      inferInstanceAs (Finite (NumberField.Units.torsion K))
    exact (Set.toFinite _).image _
  have hμF : ∀ z ∈ μ, z ∈ F → z = 1 := by
    intro z hz hzF
    obtain ⟨t, ht, rfl⟩ := (hμ_mem z).1 hz
    exact hF_tors _ hzF ⟨t, ht, by simp⟩
  have hval_tors : ∀ t : (𝓞 K)ˣ, ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuationOfNeZero (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) t) = 1 := by
    intro t v
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_unit_eq v t
  have hμA : μ ≤ A := by
    intro z hz
    obtain ⟨t, -, rfl⟩ := (hμ_mem z).1 hz
    refine ⟨fun v _ => hval_tors t v, fun v _ => ?_⟩
    rw [hval_tors t v, toAdd_one]
    exact dvd_zero _
  have hAdec : ∀ u ∈ A, ∃ z ∈ μ, ∃ φ ∈ F, u = z * φ := by
    intro u hu
    obtain ⟨t, ht, φ, hφ, h⟩ := hF_dec u ((hA_mem u).1 hu).1
    refine ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) t, (hμ_mem _).2 ⟨t, ht, rfl⟩, φ, hφ, ?_⟩
    ext
    simpa using h

  have hpos_mul : ∀ (a b : Kˣ) (w : {w : NumberField.InfinitePlace K // w.IsReal}),
      (NumberField.mixedEmbedding K ((a * b : Kˣ) : K)).1 w =
        (NumberField.mixedEmbedding K (a : K)).1 w * (NumberField.mixedEmbedding K (b : K)).1 w := by
    intro a b w
    rw [Units.val_mul, map_mul]
    rfl
  let H : Subgroup Kˣ :=
    { carrier := {φ | φ ∈ F ∧ φ ∈ A ∧
        (∀ v ∈ SK, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) φ ∈ U v) ∧
        ∀ w : {w : NumberField.InfinitePlace K // w.IsReal}, 0 < (NumberField.mixedEmbedding K (φ : K)).1 w}
      mul_mem' := by
        rintro a b ⟨haF, haA, haU, hap⟩ ⟨hbF, hbA, hbU, hbp⟩
        refine ⟨F.mul_mem haF hbF, A.mul_mem haA hbA, fun v hv => ?_, fun w => ?_⟩
        · rw [map_mul]; exact (U v).mul_mem (haU v hv) (hbU v hv)
        · rw [hpos_mul]; exact mul_pos (hap w) (hbp w)
      one_mem' := by
        refine ⟨F.one_mem, A.one_mem, fun v hv => by rw [map_one]; exact (U v).one_mem, fun w => ?_⟩
        rw [Units.val_one, map_one]
        exact one_pos
      inv_mem' := by
        rintro a ⟨haF, haA, haU, hap⟩
        refine ⟨F.inv_mem haF, A.inv_mem haA, fun v hv => by rw [map_inv]; exact (U v).inv_mem (haU v hv), fun w => ?_⟩
        have h1 : (NumberField.mixedEmbedding K ((a⁻¹ : Kˣ) : K)).1 w * (NumberField.mixedEmbedding K (a : K)).1 w = 1 := by
          rw [← hpos_mul, inv_mul_cancel, Units.val_one, map_one]
          rfl
        have := hap w
        nlinarith }
  have hH_mem : ∀ φ : Kˣ, φ ∈ H ↔ φ ∈ F ∧ φ ∈ A ∧
      (∀ v ∈ SK, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) φ ∈ U v) ∧
        ∀ w : {w : NumberField.InfinitePlace K // w.IsReal}, 0 < (NumberField.mixedEmbedding K (φ : K)).1 w :=
    fun φ => Iff.rfl
  have hHF : H ≤ F := fun φ hφ => ((hH_mem φ).1 hφ).1
  have hHA : H ≤ A := fun φ hφ => ((hH_mem φ).1 hφ).2.1
  have hcA : ∀ j, cC j ∈ A := fun j => (hA_mem _).2 ⟨fun v hv => hF_T _ (hcC j).1 v hv, (hcC j).2⟩
  have hclass' : ∀ φ ∈ F, φ ∈ A → ∃! j : Fin nC, φ * (cC j)⁻¹ ∈ H := by
    intro φ hφF hφA
    have h := hclass φ hφF ((hA_mem φ).1 hφA).2
    refine (existsUnique_congr fun j => ?_).1 h
    rw [hH_mem]
    exact ⟨fun hj => ⟨F.mul_mem hφF (F.inv_mem (hcC j).1), A.mul_mem hφA (A.inv_mem (hcA j)), hj⟩,
      fun hj => hj.2.2⟩
  obtain ⟨hIC1, hIC2⟩ :=
    Subgroup.existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem.{0, 0}
      μ F A H hμfin hμF hμA hAdec hHF hHA cC (fun j => (hcC j).1) hcA hclass'
  have hIC2ℂ : ∀ g : Kˣ → ℂ, ((A : Set Kˣ) ∩ Function.support g).Finite →
      ∑ᶠ u ∈ (A : Set Kˣ), g u = ∑ z ∈ hμfin.toFinset, ∑ j : Fin nC, ∑ᶠ h ∈ (H : Set Kˣ), g (z * cC j * h) :=
    fun g hg => hIC2 g hg
  clear hIC2

  choose Cf hCf using fun (ξ : ↥Ξ) => (hR4 ξ.1 ξ.2).2.2.2
  let Cv : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) := fun v => ⋃ ξ : ↥Ξ, Cf ξ v
  have hCv_cpt : ∀ v ∈ SK, IsCompact (Cv v) := fun v hv => isCompact_iUnion fun ξ => ((hCf ξ).1 v hv).1
  have hCv0 : ∀ v ∈ SK, (0 : v.adicCompletion K) ∉ Cv v := by
    intro v hv h
    obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.1 h
    exact ((hCf ξ).1 v hv).2 hξ
  have hvalfin : ∀ v ∈ SK, ((fun x : v.adicCompletion K => Valued.v x) '' Cv v).Finite :=
    fun v hv => Valued.finite_image_v_of_isCompact_of_zero_notMem (Cv v) (hCv_cpt v hv) (hCv0 v hv)

  let pat : Kˣ → (↥SK → WithZero (Multiplicative ℤ)) := fun u v => Valued.v ((u : K) : v.1.adicCompletion K)
  have hpat : ∀ (u : Kˣ) (v : ↥SK), pat u v = (v.1.valuationOfNeZero u : WithZero (Multiplicative ℤ)) := by
    intro u v
    simp only [pat]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  let Q : Set Kˣ := {u | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero u = 1) ∧
    (∀ v ∈ T, (f v : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u)) ∧
    ∀ v : ↥SK, ((u : K) : v.1.adicCompletion K) ∈ Cv v.1}
  have hBfin : (pat '' Q).Finite := by
    refine (Set.Finite.pi fun v : ↥SK => hvalfin v.1 v.2).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    exact Set.mem_univ_pi.2 fun v => ⟨_, hu.2.2 v, rfl⟩
  have hrep : ∀ β : ↥hBfin.toFinset, ∃ u ∈ Q, pat u = β.1 := fun β => by
    obtain ⟨u, hu, h⟩ := hBfin.mem_toFinset.1 β.2
    exact ⟨u, hu, h⟩
  choose ub hubQ hubpat using hrep

  have hβ_of : ∀ u ∈ Q, pat u ∈ hBfin.toFinset := fun u hu => hBfin.mem_toFinset.2 ⟨u, hu, rfl⟩
  have hdivA : ∀ (u : Kˣ) (hu : u ∈ Q), (ub ⟨pat u, hβ_of u hu⟩)⁻¹ * u ∈ A := by
    intro u hu
    set β : ↥hBfin.toFinset := ⟨pat u, hβ_of u hu⟩
    have hb := hubQ β
    have hpb : pat (ub β) = pat u := hubpat β
    refine (hA_mem _).2 ⟨fun v hvT => ?_, fun v hvT => ?_⟩
    · rw [map_mul, map_inv]
      by_cases hvS : v ∈ SK
      · have := congr_fun hpb ⟨v, hvS⟩
        rw [hpat, hpat] at this
        rw [WithZero.coe_inj.1 this, inv_mul_cancel]
      · rw [hb.1 v hvS hvT, hu.1 v hvS hvT, inv_one, one_mul]
    · rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
      exact dvd_add (hb.2.1 v hvT).neg_right (hu.2.1 v hvT)

  let ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
  let DISC : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun u zS =>
    ((((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                      ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                      ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                    ∏ v ∈ SK, Φf v (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                          (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) +
                  Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] *
                    ∑ v ∈ SK, (((‖((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1‖ : ℝ) : ℂ) * ((((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) *
                            AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))) * (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹)) : ℝ)) : ℂ))⁻¹ * Ψf v ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))), (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)⁻¹))) *
                      ∏ v' ∈ SK.erase v, Φf v' (((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v',
                          (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')))
  let WD : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → Kˣ → ℂ := fun ξ u =>
    ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * DISC u zS
      ∂(Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))
  let tvec : Fin T.card → ℂ := fun i => ((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1)
  let tilt : (Fin T.card → ℤ) → ℂ := fun n => ∏ i : Fin T.card, tvec i ^ (-(n i))
  let term : (Fin T.card → ℤ) → Kˣ → ℂ := fun n u => tilt n * (c' * ∑ ξ ∈ Ξ, WD ξ u)
  let I' : (Fin T.card → ℤ) → Set Kˣ := fun n => {u | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (ιK u) = 0) ∧
    ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (ιK u) = (f (T.equivFin.symm i).1 : ℤ) * n i}
  let In : (Fin T.card → ℤ) → Set Kˣ := fun n => {u | (u : K) ≠ 1 ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (ιK u) = 0) ∧
    ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (ιK u) = (f (T.equivFin.symm i).1 : ℤ) * n i}

  have hLHS : ∀ n, C * ∑ᶠ u ∈ In n, term n u = C * ∑ᶠ u ∈ In n, term n u := fun n => rfl

  have hDS : ∀ v : HeightOneSpectrum (𝓞 K), ∃ (Ψ₀ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ)
      (U₁ A : Subgroup (v.adicCompletion K)ˣ) (V : ℕ → Subgroup (v.adicCompletion K)ˣ) (sh : ℕ → Set (v.adicCompletion K)ˣ)
      (Fa : Finset (v.adicCompletion K)ˣ) (M₀ : ℕ) (C' : ℝ) (Ft : ℕ → Finset (v.adicCompletion K)ˣ)
      (c : ℕ → (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ), v ∈ SK →
      (IsLocallyConstant Ψ₀ ∧ HasCompactSupport Ψ₀ ∧
       IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
       (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
       (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, IsCompact (sh k)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
       (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
       (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
       (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
       (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧ 0 ≤ C' ∧
       (∀ a t : (v.adicCompletion K)ˣ, (∀ k, t ∉ sh k) → Ψf v (a, t) = Ψ₀ (a, t)) ∧
       (∀ k, (Ft k).card ≤ M₀) ∧
       (∀ k, ∀ τ ∈ Ft k, ∀ τ' ∈ Ft k, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
       (∀ k α τ, ‖c k α τ‖ ≤ C' * ((k : ℝ) + 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ))) ∧
       (∀ k, ∀ a t : (v.adicCompletion K)ˣ, t ∈ sh k →
          Ψf v (a, t) = Ψ₀ (a, t) + ∑ α ∈ Fa, ∑ τ ∈ Ft k, c k α τ * (if a⁻¹ * α ∈ A ∧ t⁻¹ * τ ∈ V k then 1 else 0))) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨Ψ₀, hΨ₀lc, hΨ₀cs, U₁, A, hU₁o, hAo, hAc, V, hVo, hVU, hVA, sh, hshU, hshc, hsh1, hshdisj, hshcov, hshV,
        Fa, hFa, M₀, C', hC', hoff, hshell⟩ :=
        IsDedekindDomain.HeightOneSpectrum.exists_isLocallyConstant_add_shell_defect_of_cells_of_norm_sub_le
          K v (Ψf v) (hΨf_cs v hv) (hΨf_lc v hv) (hΨf_cells v hv) (hΨf_germ v hv)
      choose Ft c hcard hsep hbd hid using hshell
      exact ⟨Ψ₀, U₁, A, V, sh, Fa, M₀, C', Ft, c, fun _ => ⟨hΨ₀lc, hΨ₀cs, hU₁o, hAo, hAc, hVo, hVU, hVA, hshU, hshc, hsh1,
        hshdisj, hshcov, hshV, hFa, hC', hoff, hcard, hsep, hbd, hid⟩⟩
    · exact ⟨0, ⊤, ⊤, fun _ => ⊤, fun _ => ∅, ∅, 0, 0, fun _ => ∅, fun _ _ _ => 0, fun h => absurd h hv⟩
  choose Ψ₀ U₁ Av Vv sh Fa M₀v C'v Ft cv hDSv using hDS

  have hbS1 : ∀ v : HeightOneSpectrum (𝓞 K),
      ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) 1 : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
    intro v; rw [map_one]; rfl
  have hN1 : ((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((1 : Kˣ) : K)) w - 1‖ ^ w.mult : ℝ)) = 0 := by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    apply Finset.prod_eq_zero (Finset.mem_univ w₀)
    have : AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((1 : Kˣ) : K)) w₀ = 1 := by
      rw [Units.val_one, map_one, map_one]; rfl
    rw [this, sub_self, norm_zero, zero_pow (NumberField.InfinitePlace.mult_pos).ne']
  have hDISC1 : ∀ zS, DISC 1 zS = 0 := by
    intro zS
    simp only [DISC, hN1, hbS1, sub_self, norm_zero, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  have hterm1 : ∀ n, term n 1 = 0 := by
    intro n
    simp only [term, WD, hDISC1, mul_zero, integral_zero, Finset.sum_const_zero]
  have hII' : ∀ n, ∑ᶠ u ∈ In n, term n u = ∑ᶠ u ∈ I' n, term n u := by
    intro n
    apply finsum_mem_inter_support_eq'
    intro u hu
    simp only [In, I', Set.mem_setOf_eq]
    have hu1 : (u : K) ≠ 1 := by
      intro h1
      have : u = 1 := Units.ext h1
      rw [Function.mem_support, this] at hu
      exact hu (hterm1 n)
    exact ⟨fun h => h.2, fun h => ⟨hu1, h⟩⟩

  have hW0 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Φ0 : (v.adicCompletion K) × (v.adicCompletion K) → ℂ, v ∈ SK →
      (IsLocallyConstant Φ0 ∧ HasCompactSupport Φ0 ∧ (∀ p, Φ0 p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
      ∀ b z : (v.adicCompletion K)ˣ, Φ0 ((b : v.adicCompletion K), (z : v.adicCompletion K)) = Ψ₀ v (z * b, b⁻¹)) := by
    intro v
    by_cases hv : v ∈ SK
    · have h := NumdDefect.isLocallyConstant_hasCompactSupport_comp_twist (Ψ₀ v) (hDSv v hv).1 (hDSv v hv).2.1
      obtain ⟨Φ0, h1, h2, h3, h4⟩ := NumCore.zeroExt K v (fun p => Ψ₀ v (p.2 * p.1, p.1⁻¹)) h.1 h.2
      exact ⟨Φ0, fun _ => ⟨h1, h2, h3, fun b z => h4 b z⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose Φ0 hΦ0 using hW0

  have hWc : ∀ (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) (α τ : (v.adicCompletion K)ˣ),
      ∃ Φc : (v.adicCompletion K) × (v.adicCompletion K) → ℂ, v ∈ SK →
      (IsLocallyConstant Φc ∧ HasCompactSupport Φc ∧ (∀ p, Φc p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
      (∀ b z : (v.adicCompletion K)ˣ, Φc ((b : v.adicCompletion K), (z : v.adicCompletion K)) =
        if (z * b)⁻¹ * α ∈ Av v ∧ b * τ ∈ Vv v k then 1 else 0) ∧
      ∀ (b z σ : (v.adicCompletion K)ˣ), σ ∈ Vv v k →
        Φc (((b * σ : (v.adicCompletion K)ˣ) : v.adicCompletion K), (z : v.adicCompletion K)) =
          Φc ((b : v.adicCompletion K), (z : v.adicCompletion K))) := by
    intro v
    rcases em (v ∈ SK) with hv | hv
    · intro k α τ
      obtain ⟨-, -, -, hAo, hAc, hVo, -, hVA, -⟩ := hDSv v hv
      let I : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ := fun p =>
        if (p.2 * p.1)⁻¹ * α ∈ Av v ∧ p.1 * τ ∈ Vv v k then 1 else 0
      have hI : IsLocallyConstant I ∧ HasCompactSupport I ∧ ∀ (b z σ : (v.adicCompletion K)ˣ), σ ∈ Vv v k → I (b * σ, z) = I (b, z) :=
        NumdDefect.cellIndicator_isLocallyConstant_hasCompactSupport_invariant (Av v) (Vv v k) hAo hAc (hVo k) (hVA k) α τ
      obtain ⟨Φc, h1, h2, h3, h4⟩ := NumCore.zeroExt K v I hI.1 hI.2.1
      refine ⟨Φc, fun _ => ⟨h1, h2, h3, fun b z => h4 b z, fun b z σ hσ => ?_⟩⟩
      rw [h4, h4]
      exact hI.2.2 b z σ hσ
    · intro k α τ
      exact ⟨0, fun h => absurd h hv⟩
  choose Φc hΦc using hWc

  have hAF := fun (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (hξ : ξ ∈ Ξ) =>
    NumberField.Idele.exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
      K νZK SK ξ (hΞc ξ hξ) Bd Cd Ed hBd_smooth hCd_smooth hEd_smooth hBd_cs hCd_cs hEd_cs CaD hCaD hBCE_Ca Φf hΦf
  choose Bt Ct Et hBCE_smooth hBCE_C₁ hBCE_lc hBCE_Cf hBCE_id using fun (ξ : ↥Ξ) => hAF ξ.1 ξ.2

  have hΦa0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' (Prod.snd '' Ca) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hΦa_Ca p (subset_tsupport _ (Function.mem_support.2 hp))
    refine ⟨q.2, ⟨q, hq, rfl⟩, ?_⟩
    rw [hpq]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, RingEquiv.symm_apply_apply]

  have hφv : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ),
      ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        (((x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := fun v x => rfl
  have hdef_off : ∀ v ∈ SK, ∀ (u : Kˣ) (zS : (AdeleRing (𝓞 K) K)ˣ),
      (∀ k, (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∉ sh v k) →
      Ψf v (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u),
            Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹) =
        Φ0 v ((((ιK u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
              (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) := by
    intro v hv u zS hoff
    rw [map_mul, map_inv, (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _ hoff, ← (hΦ0 v hv).2.2.2, hφv, hφv]
  have hdef_on : ∀ v ∈ SK, ∀ (k : ℕ) (u : Kˣ) (zS : (AdeleRing (𝓞 K) K)ˣ),
      (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∈ sh v k →
      Ψf v (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u),
            Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹) =
        Φ0 v ((((ιK u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
              (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) +
        ∑ α ∈ Fa v, ∑ τ ∈ Ft v k, cv v k α τ *
          Φc v k α τ ((((ιK u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
              (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) := by
    intro v hv k u zS hon
    rw [map_mul, map_inv, (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k _ _ hon, ← (hΦ0 v hv).2.2.2, hφv, hφv]
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← hφv v (ιK u), ← hφv v zS, (hΦc v k α τ hv).2.2.2.1]
    simp only [mul_inv_rev, inv_inv]

  let ARCH : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun u zS =>
    ((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                      ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                      ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))]))
  let emb : Kˣ → mixedEmbedding.mixedSpace K := fun u =>
    InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))
  let bS : Kˣ → ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) := fun u v =>
    (((ιK u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
  have hbS : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)), bS u v = ((u : K) : v.adicCompletion K) := fun u v => rfl

  have hratio : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 K)) (zS : (AdeleRing (𝓞 K) K)ˣ),
      ((‖bS u v - 1‖ : ℝ) : ℂ) *
        ((((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖)
            (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u))
            ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u)) *
              (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹)) *
          AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖)
            (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u))
            ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u)) *
              (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹)) : ℝ)) : ℂ))⁻¹ =
      ((Real.sqrt ‖bS u v‖ : ℝ) : ℂ) := by
    intro u hu v zS
    have ht : ((((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹)⁻¹ :
        (v.adicCompletion K)ˣ) : v.adicCompletion K)) = bS u v := by
      rw [map_inv, inv_inv]; exact hφv v (ιK u)
    have ht1 : ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹ : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) ≠ 1 := by
      have hh : ((Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹ : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) = (((u⁻¹ : Kˣ) : K) : v.adicCompletion K) := by
        rw [hφv, ← map_inv]; rfl
      rw [hh, ← NumCore.algebraMap_adicCompletion_apply, Ne,
        ← (algebraMap K (v.adicCompletion K)).map_one, (algebraMap K (v.adicCompletion K)).injective.eq_iff,
        Units.val_inv_eq_inv_val, inv_eq_one]
      exact hu
    have := NumCore.local_kink_ratio K v (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u))
      (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹) ht1
    rw [ht] at this
    exact this
  have hDISC : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
      DISC u zS = ARCH u zS * ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) +
        ∑ v ∈ SK, ((Real.sqrt ‖bS u v‖ : ℝ) : ℂ) *
          (Φa ![emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] *
            Ψf v (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u),
                  Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹) *
            ∏ v' ∈ SK.erase v, Φf v' (bS u v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')) := by
    intro u hu zS
    simp only [DISC, ARCH]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← hratio u hu v zS]
    ring

  let ΦF0 : ∀ v : HeightOneSpectrum (𝓞 K), (∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ) :=
    fun v => Function.update Φf v (Φ0 v)
  let ΦFc : ∀ (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) (α τ : (v.adicCompletion K)ˣ),
      (∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ) :=
    fun v k α τ => Function.update Φf v (Φc v k α τ)
  have hΦF0 : ∀ v ∈ SK, ∀ v' ∈ SK, IsLocallyConstant (ΦF0 v v') ∧ HasCompactSupport (ΦF0 v v') ∧
      ∀ p, ΦF0 v v' p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    intro v hv v' hv'
    by_cases h : v' = v
    · subst h
      simp only [ΦF0, Function.update_self]
      exact ⟨(hΦ0 v' hv).1, (hΦ0 v' hv).2.1, (hΦ0 v' hv).2.2.1⟩
    · simp only [ΦF0, Function.update_of_ne h]
      exact hΦf v' hv'
  have hΦFc : ∀ v ∈ SK, ∀ (k : ℕ) (α τ : (v.adicCompletion K)ˣ), ∀ v' ∈ SK,
      IsLocallyConstant (ΦFc v k α τ v') ∧ HasCompactSupport (ΦFc v k α τ v') ∧ ∀ p, ΦFc v k α τ v' p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    intro v hv k α τ v' hv'
    by_cases h : v' = v
    · subst h
      simp only [ΦFc, Function.update_self]
      exact ⟨(hΦc v' k α τ hv).1, (hΦc v' k α τ hv).2.1, (hΦc v' k α τ hv).2.2.1⟩
    · simp only [ΦFc, Function.update_of_ne h]
      exact hΦf v' hv'

  have hprodF : ∀ (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ)
      (v : HeightOneSpectrum (𝓞 K)), v ∈ SK → ∀ (W : (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
      (b z : (v' : HeightOneSpectrum (𝓞 K)) → v'.adicCompletion K),
      W (b v, z v) * ∏ v' ∈ SK.erase v, F v' (b v', z v') = ∏ v' ∈ SK, (Function.update F v W) v' (b v', z v') := by
    intro F v hv W b z
    rw [← Finset.mul_prod_erase SK (fun v' => (Function.update F v W) v' (b v', z v')) hv, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun v' hv' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv')]

  let Ga : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K → ℂ := fun q => Φa ![q.1, q.2]
  have hvec : ContDiff ℝ (⊤ : ℕ∞) (fun q : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => ![q.1, q.2]) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simpa using (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (Prod.fst : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K → _))
    · simpa using (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (Prod.snd : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K → _))
  have hGa : ContDiff ℝ (⊤ : ℕ∞) Ga := hΦa_smooth.comp hvec
  have hpair : Continuous fun p : Fin 2 → mixedEmbedding.mixedSpace K => (p 0, p 1) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hGac : HasCompactSupport Ga := by
    refine IsCompact.of_isClosed_subset (hΦa_cs.image hpair) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (hΦa_cs.image hpair).isClosed
    intro q hq
    refine ⟨![q.1, q.2], subset_tsupport _ hq, ?_⟩
    simp
  have hGa0 : ∀ (x : mixedEmbedding.mixedSpace K) (y : InfiniteAdeleRing K),
      Ga (x, InfiniteAdeleRing.ringEquiv_mixedSpace K y) ≠ 0 → y ∈ Units.val '' (Prod.snd '' Ca) := by
    intro x y h
    have := hΦa0 ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K y] h
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, RingEquiv.symm_apply_apply] at this
    exact this
  have hK7 : ∀ (ξ : ↥Ξ) (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ),
      (∀ v' ∈ SK, IsLocallyConstant (F v') ∧ HasCompactSupport (F v') ∧ ∀ p, F v' p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) →
      ∀ b : (v' : HeightOneSpectrum (𝓞 K)) → v'.adicCompletion K,
      (∀ x : mixedEmbedding.mixedSpace K, Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Ga (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v' ∈ SK, F v' (b v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')))
        (Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace K =>
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Ga (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v' ∈ SK, F v' (b v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v'))
        ∂(Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) :=
    fun ξ F hF b =>
      NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
        K νZK SK (fun z => ((ξ.1 ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) (hΞc ξ.1 ξ.2) Ga hGa hGac (Prod.snd '' Ca)
        (hCa.image continuous_snd) hGa0 F hF b

  let Wf : ↥Ξ → (∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ) →
      mixedEmbedding.mixedSpace K → ((v' : HeightOneSpectrum (𝓞 K)) → v'.adicCompletion K) → ℂ := fun ξ F x b =>
    ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (Ga (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
        ∏ v' ∈ SK, F v' (b v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v'))
      ∂(Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))

  let DI : ↥Ξ → HeightOneSpectrum (𝓞 K) → Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ := fun ξ v u zS =>
    ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (Φa ![emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] *
        Ψf v (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (zS * ιK u),
              Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u)⁻¹) *
        ∏ v' ∈ SK.erase v, Φf v' (bS u v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v'))
  have hGa_apply : ∀ (u : Kˣ) (zS : (AdeleRing (𝓞 K) K)ˣ),
      Φa ![emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] =
        Ga (emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) := fun u zS => rfl
  have hDoff : ∀ v ∈ SK, ∀ (u : Kˣ), (∀ k, (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∉ sh v k) →
      ∀ ξ : ↥Ξ, (fun zS => DI ξ v u zS) = fun zS => ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        (Ga (emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
          ∏ v' ∈ SK, ΦF0 v v' (bS u v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')) := by
    intro v hv u hoff ξ
    funext zS
    simp only [DI]
    rw [hdef_off v hv u zS hoff, hGa_apply, mul_assoc (Ga _),
      hprodF Φf v hv (Φ0 v) (bS u) (fun v' => (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')]
  have hDon : ∀ v ∈ SK, ∀ (k : ℕ) (u : Kˣ), (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∈ sh v k →
      ∀ ξ : ↥Ξ, (fun zS => DI ξ v u zS) = fun zS =>
        ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Ga (emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v' ∈ SK, ΦF0 v v' (bS u v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')) +
        ∑ α ∈ Fa v, ∑ τ ∈ Ft v k, cv v k α τ *
          (((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (Ga (emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
              ∏ v' ∈ SK, ΦFc v k α τ v' (bS u v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v'))) := by
    intro v hv k u hon ξ
    funext zS
    simp only [DI]
    rw [hdef_on v hv k u zS hon, hGa_apply]
    simp only [ΦF0, ΦFc, ← hprodF Φf v hv _ (bS u) (fun v' => (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v')]
    rw [mul_add, add_mul, mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring

  have hDI_off : ∀ v ∈ SK, ∀ (u : Kˣ), (∀ k, (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∉ sh v k) →
      ∀ ξ : ↥Ξ, Integrable (DI ξ v u) (Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) ∧
        (∫ zS, DI ξ v u zS ∂(Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
          Wf ξ (ΦF0 v) (emb u) (bS u) := by
    intro v hv u hoff ξ
    have h := hDoff v hv u hoff ξ
    refine ⟨?_, ?_⟩
    · rw [show DI ξ v u = fun zS => DI ξ v u zS from rfl, h]
      exact (hK7 ξ (ΦF0 v) (hΦF0 v hv) (bS u)).1 (emb u)
    · simp only [Wf]
      rw [show (fun zS => DI ξ v u zS) = _ from h]
  have hDI_on : ∀ v ∈ SK, ∀ (k : ℕ) (u : Kˣ), (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∈ sh v k →
      ∀ ξ : ↥Ξ, Integrable (DI ξ v u) (Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) ∧
        (∫ zS, DI ξ v u zS ∂(Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
          Wf ξ (ΦF0 v) (emb u) (bS u) + ∑ α ∈ Fa v, ∑ τ ∈ Ft v k, cv v k α τ * Wf ξ (ΦFc v k α τ) (emb u) (bS u) := by
    intro v hv k u hon ξ
    have h := hDon v hv k u hon ξ
    have I0 := (hK7 ξ (ΦF0 v) (hΦF0 v hv) (bS u)).1 (emb u)
    have Ic : ∀ α τ, Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => cv v k α τ * (((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        (Ga (emb u, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
          ∏ v' ∈ SK, ΦFc v k α τ v' (bS u v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v'))))
        (Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) :=
      fun α τ => ((hK7 ξ (ΦFc v k α τ) (hΦFc v hv k α τ) (bS u)).1 (emb u)).const_mul _
    have Isum := integrable_finset_sum (Fa v) fun α _ => integrable_finset_sum (Ft v k) fun τ _ => Ic α τ
    refine ⟨?_, ?_⟩
    · rw [show DI ξ v u = fun zS => DI ξ v u zS from rfl, h]
      exact I0.add Isum
    · rw [show (fun zS => DI ξ v u zS) = _ from h, integral_add I0 Isum, integral_finset_sum _ (fun α _ =>
        integrable_finset_sum (Ft v k) fun τ _ => Ic α τ)]
      simp only [Wf]
      congr 1
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [integral_finset_sum _ (fun τ _ => Ic α τ)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      exact integral_const_mul _ _
  have hDI_int : ∀ v ∈ SK, ∀ (u : Kˣ) (ξ : ↥Ξ), Integrable (DI ξ v u) (Measure.map (NumberField.Idele.partAt K SK)
      (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) := by
    intro v hv u ξ
    rcases em (∃ k, (Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u))⁻¹ ∈ sh v k) with ⟨k, hk⟩ | hno
    · exact (hDI_on v hv k u hk ξ).1
    · exact (hDI_off v hv u (fun k hk => hno ⟨k, hk⟩) ξ).1

  have hWD : ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ ξ : ↥Ξ,
      WD ξ.1 u = (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (ARCH u zS * ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) +
        ∑ v ∈ SK, ((Real.sqrt ‖bS u v‖ : ℝ) : ℂ) * ∫ zS, DI ξ v u zS ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) := by
    intro u hu ξ
    have hA := ((hBCE_id ξ) u hu (bS u)).1
    have hpt : (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * DISC u zS) =
        fun zS => ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (ARCH u zS * ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) +
          ∑ v ∈ SK, ((Real.sqrt ‖bS u v‖ : ℝ) : ℂ) * DI ξ v u zS := by
      funext zS
      rw [hDISC u hu zS, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [DI]
      ring
    have hS : Integrable (fun zS => ∑ v ∈ SK, ((Real.sqrt ‖bS u v‖ : ℝ) : ℂ) * DI ξ v u zS)
        (Measure.map (NumberField.Idele.partAt K SK)
          (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) :=
      integrable_finset_sum SK fun v hv => (hDI_int v hv u ξ).const_mul _
    show (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * DISC u zS ∂_) = _
    rw [hpt, integral_add hA hS, integral_finset_sum SK (fun v hv => (hDI_int v hv u ξ).const_mul _)]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    exact integral_const_mul _ _

  have hemb : ∀ u : Kˣ, emb u = NumberField.mixedEmbedding K (u : K) := fun u => NumCore.emb_eq K u
  have hLog1 : ∀ (u : Kˣ) (w : InfinitePlace K), (Log u).1 (Fintype.equivFin (InfinitePlace K) w) =
      (w.mult : ℝ) * Real.log (mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K (u : K))) := by
    intro u w
    rw [hLog]
    simp only [Equiv.symm_apply_apply, NumberField.mixedEmbedding.normAtPlace_apply]
  have hKR : ∀ (u : Kˣ) (w : InfinitePlace K) (hw : w.IsReal),
      ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
        if sgn (emb u) ⟨w, hw⟩ = 1
        then Real.exp (-((Log u).1 (Fintype.equivFin (InfinitePlace K) w))) * |1 - Real.exp ((Log u).1 (Fintype.equivFin (InfinitePlace K) w))|
        else 1 + Real.exp (-((Log u).1 (Fintype.equivFin (InfinitePlace K) w))) := by
    intro u w hw
    rw [PccKink.kinkScalar_real K P sgn arg hP_inv hP_fst u w hw]
    simp only [Equiv.symm_apply_apply, hemb, hLog1]
  have hKC : ∀ (u : Kˣ) (w : InfinitePlace K) (hw : w.IsComplex),
      ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
        Real.exp (-((Log u).1 (Fintype.equivFin (InfinitePlace K) w) / 2)) *
          ‖(1 : ℂ) - Complex.exp ((((Log u).1 (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * ((arg (emb u) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ ∧
      ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 *
        Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ =
        Real.exp (-((Log u).1 (Fintype.equivFin (InfinitePlace K) w))) *
          (‖(1 : ℂ) - Complex.exp ((((Log u).1 (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((arg (emb u) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((((Log u).1 (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((arg (emb u) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ -
          (Log u).1 (Fintype.equivFin (InfinitePlace K) w) / 2 *
            ‖(1 : ℂ) - Complex.exp ((((Log u).1 (Fintype.equivFin (InfinitePlace K) w) / 2 : ℝ) : ℂ) +
              2 * Real.pi * Complex.I * ((arg (emb u) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2) := by
    intro u w hw
    have h := PccKink.kinkScalar_complex K P sgn arg hP_inv hP_snd u w hw
    simp only [Equiv.symm_apply_apply] at h
    simp only [hemb, hLog1]
    exact h

  have hR4F := fun (ξ : ↥Ξ) (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ)
      (hF : ∀ v' ∈ SK, IsLocallyConstant (F v') ∧ HasCompactSupport (F v') ∧ ∀ p, F v' p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) =>
    NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
      K νZK SK ξ.1 (hΞc ξ.1 ξ.2) Φa hΦa_smooth hΦa_cs (Prod.snd '' Ca) (hCa.image continuous_snd) hΦa0 F hF

  let C₀ : Set (mixedEmbedding.mixedSpace K) :=
    (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) '' Ca
  have hC₀ : IsCompact C₀ :=
    hCa.image ((NumCore.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.comp continuous_fst))
  have hC₀u : ∀ y ∈ C₀, IsUnit y := by
    rintro _ ⟨q, -, rfl⟩
    exact q.1.isUnit.map _
  have hWf0 : ∀ (ξ : ↥Ξ) (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ)
      (x : mixedEmbedding.mixedSpace K) b, Wf ξ F x b ≠ 0 → x ∈ C₀ := by
    intro ξ F x b hne
    by_contra hx
    apply hne
    have hzero : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        Ga (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) = 0 := by
      intro zS
      by_contra hΦ
      obtain ⟨q, hq, hpq⟩ := hΦa_Ca _ (subset_tsupport _ (Function.mem_support.2 hΦ))
      have h0 := congr_fun hpq 0
      simp only [Matrix.cons_val_zero] at h0
      exact hx ⟨q, hq, h0.symm⟩
    simp only [Wf, hzero, mul_zero, zero_mul, integral_zero]

  have hLC0 : ∀ v : HeightOneSpectrum (𝓞 K), ∃ U₀ : Subgroup (v.adicCompletion K)ˣ, v ∈ SK →
      (IsOpen (U₀ : Set (v.adicCompletion K)ˣ) ∧
        ∀ t ∈ U₀, ∀ b z : v.adicCompletion K, Φ0 v (b * (t : v.adicCompletion K), z) = Φ0 v (b, z)) := by
    intro v
    by_cases hv : v ∈ SK
    · obtain ⟨U₀, h⟩ :=
        IsDedekindDomain.HeightOneSpectrum.exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
          K v (Φ0 v) (hΦ0 v hv).1 (hΦ0 v hv).2.1 (hΦ0 v hv).2.2.1
      exact ⟨U₀, fun _ => h⟩
    · exact ⟨⊤, fun h => absurd h hv⟩
  choose U0 hU0 using hLC0
  let Us : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ := fun v => (U v ⊓ U0 v) ⊓ Av v
  have hUs_open : ∀ v ∈ SK, IsOpen (Us v : Set (v.adicCompletion K)ˣ) := fun v hv =>
    ((hU v hv).1.inter (hU0 v hv).1).inter (hDSv v hv).2.2.2.1
  have hUs_U : ∀ v, Us v ≤ U v := fun v t ht => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ht).1).1
  have hUs_U0 : ∀ v, Us v ≤ U0 v := fun v t ht => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ht).1).2
  have hUs_A : ∀ v, Us v ≤ Av v := fun v t ht => (Subgroup.mem_inf.1 ht).2
  obtain ⟨nCs, cCs, hcCs, hclassS⟩ := hF_classes (fun v => (f v : ℤ)) SK hST Us hUs_open
  let Hs : Subgroup Kˣ :=
    { carrier := {φ | φ ∈ F ∧ φ ∈ A ∧
        (∀ v ∈ SK, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) φ ∈ Us v) ∧
        ∀ w : {w : NumberField.InfinitePlace K // w.IsReal}, 0 < (NumberField.mixedEmbedding K (φ : K)).1 w}
      mul_mem' := by
        rintro a b ⟨haF, haA, haU, hap⟩ ⟨hbF, hbA, hbU, hbp⟩
        refine ⟨F.mul_mem haF hbF, A.mul_mem haA hbA, fun v hv => ?_, fun w => ?_⟩
        · rw [map_mul]; exact (Us v).mul_mem (haU v hv) (hbU v hv)
        · rw [hpos_mul]; exact mul_pos (hap w) (hbp w)
      one_mem' := by
        refine ⟨F.one_mem, A.one_mem, fun v hv => by rw [map_one]; exact (Us v).one_mem, fun w => ?_⟩
        rw [Units.val_one, map_one]
        exact one_pos
      inv_mem' := by
        rintro a ⟨haF, haA, haU, hap⟩
        refine ⟨F.inv_mem haF, A.inv_mem haA, fun v hv => by rw [map_inv]; exact (Us v).inv_mem (haU v hv), fun w => ?_⟩
        have h1 : (NumberField.mixedEmbedding K ((a⁻¹ : Kˣ) : K)).1 w * (NumberField.mixedEmbedding K (a : K)).1 w = 1 := by
          rw [← hpos_mul, inv_mul_cancel, Units.val_one, map_one]
          rfl
        have := hap w
        nlinarith }
  have hHs_mem : ∀ φ : Kˣ, φ ∈ Hs ↔ φ ∈ F ∧ φ ∈ A ∧
      (∀ v ∈ SK, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) φ ∈ Us v) ∧
        ∀ w : {w : NumberField.InfinitePlace K // w.IsReal}, 0 < (NumberField.mixedEmbedding K (φ : K)).1 w :=
    fun φ => Iff.rfl
  have hHsF : Hs ≤ F := fun φ hφ => ((hHs_mem φ).1 hφ).1
  have hHsA : Hs ≤ A := fun φ hφ => ((hHs_mem φ).1 hφ).2.1
  have hcAs : ∀ j, cCs j ∈ A := fun j => (hA_mem _).2 ⟨fun v hv => hF_T _ (hcCs j).1 v hv, (hcCs j).2⟩
  have hclassS' : ∀ φ ∈ F, φ ∈ A → ∃! j : Fin nCs, φ * (cCs j)⁻¹ ∈ Hs := by
    intro φ hφF hφA
    have h := hclassS φ hφF ((hA_mem φ).1 hφA).2
    refine (existsUnique_congr fun j => ?_).1 h
    rw [hHs_mem]
    exact ⟨fun hj => ⟨F.mul_mem hφF (F.inv_mem (hcCs j).1), A.mul_mem hφA (A.inv_mem (hcAs j)), hj⟩,
      fun hj => hj.2.2⟩
  obtain ⟨-, hICs⟩ :=
    Subgroup.existsUnique_eq_mul_mul_and_finsum_mem_eq_sum_sum_finsum_mem_of_existsUnique_mul_inv_mem.{0, 0}
      μ F A Hs hμfin hμF hμA hAdec hHsF hHsA cCs (fun j => (hcCs j).1) hcAs hclassS'
  have hICsℂ : ∀ g : Kˣ → ℂ, ((A : Set Kˣ) ∩ Function.support g).Finite →
      ∑ᶠ u ∈ (A : Set Kˣ), g u = ∑ z ∈ hμfin.toFinset, ∑ j : Fin nCs, ∑ᶠ h ∈ (Hs : Set Kˣ), g (z * cCs j * h) :=
    fun g hg => hICs g hg
  clear hICs

  have htsupp_lc : ∀ (v : HeightOneSpectrum (𝓞 K)) (g : (v.adicCompletion K) × (v.adicCompletion K) → ℂ),
      IsLocallyConstant g → tsupport g = Function.support g := by
    intro v g hg
    have hcl : IsClosed (Function.support g) := by
      have : Function.support g = (g ⁻¹' {0})ᶜ := by
        ext x; simp [Function.mem_support]
      rw [this, isClosed_compl_iff]
      exact hg.isOpen_fiber 0
    exact hcl.closure_eq

  choose CfA hCfA using hBCE_Cf
  let Dv : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v =>
    (Prod.snd '' (tsupport (Ψf v) ∪ tsupport (Ψ₀ v)))⁻¹
  let Cst : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) := fun v =>
    ((Prod.fst '' tsupport (Φf v) ∪ Prod.fst '' tsupport (Φ0 v)) ∪ ⋃ ξ : ↥Ξ, CfA ξ v) ∪ Units.val '' Dv v
  have hDv_cpt : ∀ v ∈ SK, IsCompact (Dv v) := fun v hv =>
    (((hΨf_cs v hv).union (hDSv v hv).2.1).image continuous_snd).inv
  have hCst_cpt : ∀ v ∈ SK, IsCompact (Cst v) := by
    intro v hv
    refine ((((hΦf v hv).2.1.image continuous_fst).union ((hΦ0 v hv).2.1.image continuous_fst)).union
      (isCompact_iUnion fun ξ => ((hCfA ξ).1 v hv).1)).union ((hDv_cpt v hv).image Units.continuous_val)
  have hCst0 : ∀ v ∈ SK, (0 : v.adicCompletion K) ∉ Cst v := by
    intro v hv h0
    rcases h0 with ((h0 | h0) | h0) | h0
    · obtain ⟨p, hp, hp0⟩ := h0
      rw [htsupp_lc v _ (hΦf v hv).1] at hp
      exact ((hΦf v hv).2.2 p hp).1 hp0
    · obtain ⟨p, hp, hp0⟩ := h0
      rw [htsupp_lc v _ (hΦ0 v hv).1] at hp
      exact ((hΦ0 v hv).2.2.1 p hp).1 hp0
    · obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.1 h0
      exact ((hCfA ξ).1 v hv).2 hξ
    · obtain ⟨t, ht1, ht⟩ := h0
      exact Units.ne_zero t ht
  have hvalfinS : ∀ v ∈ SK, ((fun x : v.adicCompletion K => Valued.v x) '' Cst v).Finite :=
    fun v hv => Valued.finite_image_v_of_isCompact_of_zero_notMem (Cst v) (hCst_cpt v hv) (hCst0 v hv)
  let Qs : Set Kˣ := {u | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero u = 1) ∧
    (∀ v ∈ T, (f v : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u)) ∧
    ∀ v : ↥SK, ((u : K) : v.1.adicCompletion K) ∈ Cst v.1}
  have hBfinS : (pat '' Qs).Finite := by
    refine (Set.Finite.pi fun v : ↥SK => hvalfinS v.1 v.2).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    exact Set.mem_univ_pi.2 fun v => ⟨_, hu.2.2 v, rfl⟩
  have hrepS : ∀ β : ↥hBfinS.toFinset, ∃ u ∈ Qs, pat u = β.1 := fun β => by
    obtain ⟨u, hu, h⟩ := hBfinS.mem_toFinset.1 β.2
    exact ⟨u, hu, h⟩
  choose ubS hubQS hubpatS using hrepS
  have hβ_ofS : ∀ u ∈ Qs, pat u ∈ hBfinS.toFinset := fun u hu => hBfinS.mem_toFinset.2 ⟨u, hu, rfl⟩
  have hdivAS : ∀ (u : Kˣ) (hu : u ∈ Qs), (ubS ⟨pat u, hβ_ofS u hu⟩)⁻¹ * u ∈ A := by
    intro u hu
    set β : ↥hBfinS.toFinset := ⟨pat u, hβ_ofS u hu⟩
    have hb := hubQS β
    have hpb : pat (ubS β) = pat u := hubpatS β
    refine (hA_mem _).2 ⟨fun v hvT => ?_, fun v hvT => ?_⟩
    · rw [map_mul, map_inv]
      by_cases hvS : v ∈ SK
      · have := congr_fun hpb ⟨v, hvS⟩
        rw [hpat, hpat] at this
        rw [WithZero.coe_inj.1 this, inv_mul_cancel]
      · rw [hb.1 v hvS hvT, hu.1 v hvS hvT, inv_one, one_mul]
    · rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
      exact dvd_add (hb.2.1 v hvT).neg_right (hu.2.1 v hvT)

  have hWf_supp : ∀ (ξ : ↥Ξ) (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ)
      (x : mixedEmbedding.mixedSpace K) (b : (v' : HeightOneSpectrum (𝓞 K)) → v'.adicCompletion K),
      Wf ξ F x b ≠ 0 → ∀ v ∈ SK, ∃ z : v.adicCompletion K, F v (b v, z) ≠ 0 := by
    intro ξ F x b hne v hv
    by_contra hall
    push_neg at hall
    apply hne
    have hzero : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        ∏ v' ∈ SK, F v' (b v', (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v') = 0 :=
      fun zS => Finset.prod_eq_zero hv (hall _)
    simp only [Wf, hzero, mul_zero, integral_zero]
  have hfst_tsupp : ∀ (v : HeightOneSpectrum (𝓞 K)) (g : (v.adicCompletion K) × (v.adicCompletion K) → ℂ) (b z : v.adicCompletion K),
      g (b, z) ≠ 0 → b ∈ Prod.fst '' tsupport g :=
    fun v g b z h => ⟨(b, z), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

  have hemb_mul : ∀ a b : Kˣ, emb (a * b) = emb a * emb b := by
    intro a b; rw [hemb, hemb, hemb, Units.val_mul, map_mul]
  have hemb_unit : ∀ u : Kˣ, IsUnit (emb u) := fun u => by rw [hemb]; exact u.isUnit.map _
  have hbS : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)), bS u v = ((u : K) : v.adicCompletion K) := fun u v => rfl
  have htvec : ∀ i, tvec i ≠ 0 := by
    intro i
    have hvT : (T.equivFin.symm i).1 ∈ T := (T.equivFin.symm i).2
    refine mul_ne_zero ?_ fun h => hζ _ hvT (by rw [← hs _ hvT, h]; ring)
    have hN : (0 : ℝ) < (Nw (T.equivFin.symm i).1 : ℝ) := by
      rw [hNwf _ hvT]
      have : Ideal.absNorm (T.equivFin.symm i).1.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact (T.equivFin.symm i).1.ne_bot
      positivity
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'

  let Xw : mixedEmbedding.mixedSpace K → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) := fun y i =>
    (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
      Real.log (mixedEmbedding.normAtPlace ((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) y)
  have hXw : ∀ u : Kˣ, Xw (emb u) = (Log u).1 := by
    intro u
    rw [hLog, hemb]
    funext i
    simp only [Xw, NumberField.mixedEmbedding.normAtPlace_apply]
  have hP_inv' : ∀ u : Kˣ, P (sgn (emb u)) ((Log u).1, arg (emb u)) = emb u := by
    intro u
    rw [← hXw]
    exact hP_inv (emb u) (hemb_unit u)
  have hP_mul' : ∀ σ (x x' : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)
      (θ θ' : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → ℝ), P σ (x + x', θ + θ') = P σ (x, θ) * P 1 (x', θ') := by
    intro σ x x' θ θ'
    have := hP_mul σ 1 x x' θ θ'
    rwa [mul_one] at this
  have hP_bdd' : ∀ σ (C₁ : Set (mixedEmbedding.mixedSpace K)), IsCompact C₁ → (∀ y ∈ C₁, IsUnit y) →
      ∃ R : ℝ, ∀ (x : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)
        (θ : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → ℝ), P σ (x, θ) ∈ C₁ → ∀ i, |x i| ≤ R :=
    fun σ C₁ hC hu => (hP_bdd C₁ hC hu).imp fun R hR x θ => hR σ x θ

  let Lmap : Kˣ → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) := fun u =>
    ((Log u).1, fun j => -((Log u).2 j / (f (T.equivFin.symm j).1 : ℤ)))
  have hLog2 : ∀ (u : Kˣ) (j : Fin T.card), (Log u).2 j = Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u) := by
    intro u j; rw [hLog]
  have hfdvd : ∀ u ∈ A, ∀ j : Fin T.card, (f (T.equivFin.symm j).1 : ℤ) ∣ (Log u).2 j := by
    intro u hu j
    rw [hLog2]
    exact ((hA_mem u).1 hu).2 _ (T.equivFin.symm j).2
  have hf0 : ∀ j : Fin T.card, (f (T.equivFin.symm j).1 : ℤ) ≠ 0 := fun j => by
    have := hf _ (T.equivFin.symm j).2; omega
  let FA : Subgroup Kˣ := F ⊓ A
  have hL_add : ∀ φ ∈ FA, ∀ ψ ∈ FA, Lmap (φ * ψ) = Lmap φ + Lmap ψ := by
    intro φ hφ ψ hψ
    simp only [Lmap, hLog_mul, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    funext j
    simp only [Pi.add_apply]
    rw [Int.add_ediv_of_dvd_left (hfdvd φ (Subgroup.mem_inf.1 hφ).2 j)]
    ring
  have hLog_tors : ∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
      (Log u = 0 ↔ ∃ t : (𝓞 K)ˣ, t ∈ NumberField.Units.torsion K ∧ ((t : 𝓞 K) : K) = (u : K)) := by
    intro u hu
    rw [← hLog₁eq]
    exact hΛ₁_tors u hu
  have hL_inj : ∀ φ ∈ FA, Lmap φ = 0 → φ = 1 := by
    intro φ hφ h0
    have hφF := (Subgroup.mem_inf.1 hφ).1
    have hφA := (Subgroup.mem_inf.1 hφ).2
    have h1 : (Log φ).1 = 0 := congrArg Prod.fst h0
    have h2 : ∀ j, (Log φ).2 j = 0 := by
      intro j
      have hj : -((Log φ).2 j / (f (T.equivFin.symm j).1 : ℤ)) = 0 := congr_fun (congrArg Prod.snd h0) j
      have hd := hfdvd φ hφA j
      rw [neg_eq_zero] at hj
      rw [← Int.mul_ediv_cancel' hd, hj, mul_zero]
    have hL0 : Log φ = 0 := Prod.ext h1 (funext h2)
    exact hF_tors φ hφF ((hLog_tors φ ((hA_mem φ).1 hφA).1).1 hL0)
  have hΛ' : ∀ γ, γ ∈ Λ ↔ ∃ φ ∈ FA, Lmap φ = γ := by
    intro γ
    rw [hΛ_mem, hΛf_mem]
    constructor
    · rintro ⟨u, huT, hu⟩
      have huA : u ∈ A := by
        refine (hA_mem u).2 ⟨huT, fun v hv => ?_⟩
        have := congr_fun (congrArg Prod.snd hu) (T.equivFin ⟨v, hv⟩)
        rw [hLog2] at this
        simp only [Equiv.symm_apply_apply] at this
        rw [this]
        exact Dvd.intro _ rfl
      obtain ⟨z, hz, φ, hφ, rfl⟩ := hAdec u huA
      have hzL : Log z = 0 := by
        obtain ⟨t, ht, rfl⟩ := (hμ_mem z).1 hz
        exact (hLog_tors _ (fun v _ => hval_tors t v)).2 ⟨t, ht, by simp⟩
      have hφA : φ ∈ A := by
        have : z⁻¹ * (z * φ) ∈ A := A.mul_mem (A.inv_mem (hμA hz)) huA
        simpa using this
      refine ⟨φ, Subgroup.mem_inf.2 ⟨hφ, hφA⟩, ?_⟩
      rw [hLog_mul, hzL, zero_add] at hu
      simp only [Lmap]
      refine Prod.ext (by simpa using congrArg Prod.fst hu) (funext fun j => ?_)
      have := congr_fun (congrArg Prod.snd hu) j
      simp only at this
      show -((Log φ).2 j / (f (T.equivFin.symm j).1 : ℤ)) = γ.2 j
      rw [this, Pi.neg_apply, mul_neg, Int.neg_ediv_of_dvd (Dvd.intro _ rfl), neg_neg,
        Int.mul_ediv_cancel_left _ (hf0 j)]
    · rintro ⟨φ, hφ, rfl⟩
      have hφA := (Subgroup.mem_inf.1 hφ).2
      refine ⟨φ, ((hA_mem φ).1 hφA).1, Prod.ext rfl (funext fun j => ?_)⟩
      simp only [Lmap, Pi.neg_apply, neg_neg]
      rw [Int.mul_ediv_cancel' (hfdvd φ hφA j)]
  let bvec : Fin T.card → ℝ := fun j => -(tvec j).arg / (2 * Real.pi)
  obtain ⟨χ, lift, hlift0, hcompat, hliftF⟩ :=
    NumberField.mixedEmbedding.exists_addMonoidHom_addCircle_lift_arg_of_injOn K arg
      (fun y y' hy hy' => (hP_sgnarg y y' hy hy').2) FA Lmap hL_add hL_inj Λ hΛ' bvec

  have hL_one : Lmap 1 = 0 := by
    have := hL_add 1 FA.one_mem 1 FA.one_mem
    rw [mul_one] at this
    have h2 : Lmap 1 + Lmap 1 = Lmap 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h2
  have hL_inv : ∀ h ∈ FA, Lmap h⁻¹ = -Lmap h := by
    intro h hh
    have := hL_add h⁻¹ (FA.inv_mem hh) h hh
    rw [inv_mul_cancel, hL_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hHsFA : Hs ≤ FA := fun h hh => Subgroup.mem_inf.2 ⟨hHsF hh, hHsA hh⟩
  let cs : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) :=
    fun j => Fin.castAdd T.card (Fintype.equivFin (NumberField.InfinitePlace K)
      ((Fintype.equivFin {w : NumberField.InfinitePlace K // w.IsComplex}).symm j).1)
  let ts : Fin T.card → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) :=
    fun j => Fin.natAdd (Fintype.card (NumberField.InfinitePlace K)) j
  have hord : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)),
      NumberField.Idele.ord K v (ιK u) = -Multiplicative.toAdd (v.valuationOfNeZero u) := fun u v => NumCore.ord_unitsMap K u v
  have hLog_one : Log 1 = 0 := by
    have := hLog_mul 1 1
    rw [mul_one] at this
    have h2 : Log 1 + Log 1 = Log 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h2
  have hLog_inv : ∀ a : Kˣ, Log a⁻¹ = -Log a := fun a => by
    have := hLog_mul a⁻¹ a
    rw [inv_mul_cancel, hLog_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hI'_val : ∀ (n : Fin T.card → ℤ) (u : Kˣ), u ∈ I' n ↔ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero u = 1) ∧
      ∀ i : Fin T.card, (Log u).2 i = -((f (T.equivFin.symm i).1 : ℤ) * n i) := by
    intro n u
    simp only [I', Set.mem_setOf_eq, hord, hLog2]
    refine and_congr (forall_congr' fun v => forall_congr' fun _ => forall_congr' fun _ => ?_)
      (forall_congr' fun i => ?_)
    · rw [neg_eq_zero, toAdd_eq_zero]
    · constructor <;> intro h <;> linarith

  have hLS : ∀ H' : Subgroup Kˣ, H' ≤ FA → ∃ S : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      S ≤ Λ ∧ (∀ γ, γ ∈ S ↔ ∃ h ∈ H', Lmap h = γ) ∧
      ∀ Ψ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → ℂ,
        (Function.support Ψ ∩ (S : Set _)).Finite → ∑ᶠ h ∈ (H' : Set Kˣ), Ψ (Lmap h) = ∑' γ : S, Ψ (γ : _) := by
    intro H' hH'
    let S : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
      { carrier := {γ | ∃ h ∈ H', Lmap h = γ}
        zero_mem' := ⟨1, H'.one_mem, hL_one⟩
        add_mem' := by
          rintro a b ⟨h, hh, rfl⟩ ⟨h', hh', rfl⟩
          exact ⟨h * h', H'.mul_mem hh hh', hL_add h (hH' hh) h' (hH' hh')⟩
        neg_mem' := by
          rintro a ⟨h, hh, rfl⟩
          exact ⟨h⁻¹, H'.inv_mem hh, hL_inv h (hH' hh)⟩ }
    have hS_mem : ∀ γ, γ ∈ S ↔ ∃ h ∈ H', Lmap h = γ := fun γ => Iff.rfl
    refine ⟨S, ?_, hS_mem, fun Ψ hfin => ?_⟩
    · rintro γ ⟨h, hh, rfl⟩
      exact (hΛ' _).2 ⟨h, hH' hh, rfl⟩
    have hinj : Set.InjOn Lmap (H' : Set Kˣ) := by
      intro a ha b hb hab
      have h0 : Lmap (a * b⁻¹) = 0 := by
        rw [hL_add a (hH' ha) b⁻¹ (FA.inv_mem (hH' hb)), hL_inv b (hH' hb), hab, add_neg_cancel]
      have := hL_inj _ (FA.mul_mem (hH' ha) (FA.inv_mem (hH' hb))) h0
      rw [mul_inv_eq_one] at this
      exact this
    have hbij : Set.BijOn Lmap (H' : Set Kˣ) (S : Set _) := by
      refine ⟨fun h hh => ?_, hinj, fun γ hγ => ?_⟩
      · rw [SetLike.mem_coe, hS_mem]
        exact ⟨h, hh, rfl⟩
      · rw [SetLike.mem_coe, hS_mem] at hγ
        obtain ⟨h, hh, hγ⟩ := hγ
        exact ⟨h, hh, hγ⟩
    have h1 : ∑ᶠ h ∈ (H' : Set Kˣ), Ψ (Lmap h) = ∑ᶠ γ ∈ (S : Set _), Ψ γ :=
      finsum_mem_eq_of_bijOn _ hbij (fun _ _ => rfl)
    have hfinΨ : (Function.support fun γ : S => Ψ (γ : _)).Finite := by
      refine (hfin.preimage (Subtype.val_injective.injOn)).subset ?_
      intro γ hγ
      exact ⟨hγ, γ.2⟩
    rw [h1, ← finsum_set_coe_eq_finsum_mem, tsum_eq_finsum hfinΨ]
    rfl

  have hfib : ∀ γ, {a : Kˣ | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero a = 1) ∧ Log a = γ}.Finite := by
    intro γ
    by_cases hne : ∃ a₀ : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero a₀ = 1) ∧ Log a₀ = γ
    · obtain ⟨a₀, ha₀, rfl⟩ := hne
      haveI : Finite ((NumberField.Units.torsion K : Subgroup (𝓞 K)ˣ) : Set (𝓞 K)ˣ) :=
        inferInstanceAs (Finite (NumberField.Units.torsion K))
      refine ((Set.toFinite ((NumberField.Units.torsion K : Subgroup (𝓞 K)ˣ) : Set (𝓞 K)ˣ)).image
        fun t => Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) t * a₀).subset ?_
      rintro a ⟨ha, hLa⟩
      have hq : Log (a * a₀⁻¹) = 0 := by rw [hLog_mul, hLog_inv, hLa, add_neg_cancel]
      have hqT : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero (a * a₀⁻¹) = 1 := fun v hv => by
        rw [map_mul, map_inv, ha v hv, ha₀ v hv, inv_one, mul_one]
      obtain ⟨t, ht, hta⟩ := (hLog_tors _ hqT).1 hq
      refine ⟨t, ht, ?_⟩
      have : Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) t = a * a₀⁻¹ := by ext; simpa using hta
      show Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) t * a₀ = a
      rw [this, inv_mul_cancel_right]
    · refine Set.Finite.subset Set.finite_empty fun a ha => hne ⟨a, ha⟩
  have hboxfin : ∀ (R : ℝ) (k₀ : Fin T.card → ℤ),
      {a : Kˣ | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero a = 1) ∧ (∀ i, |(Log a).1 i| ≤ R) ∧ (Log a).2 = k₀}.Finite := by
    intro R k₀
    haveI := hΛ₁_disc
    have hΦ := AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology Λ₁ R k₀
    refine (hΦ.biUnion fun γ _ => hfib γ).subset ?_
    rintro a ⟨ha, hbox, hk⟩
    refine Set.mem_biUnion (x := Log a) ⟨(hΛ₁_mem _).2 ⟨a, ha, hLog₁eq a⟩, hbox, hk⟩ ⟨ha, rfl⟩

  choose C₁ hC₁ using hBCE_C₁
  let Call : Set (mixedEmbedding.mixedSpace K) := C₀ ∪ ⋃ ξ : ↥Ξ, C₁ ξ
  have hCall : IsCompact Call := hC₀.union (isCompact_iUnion fun ξ => (hC₁ ξ).1)
  have hCallu : ∀ y ∈ Call, IsUnit y := by
    rintro y (hy | hy)
    · exact hC₀u y hy
    · obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.1 hy
      exact (hC₁ ξ).2.1 y hξ
  obtain ⟨R₀, hR₀⟩ := hP_bdd Call hCall hCallu

  have hSfinG : ∀ (n : Fin T.card → ℤ) (g : Kˣ → ℂ),
      (∀ u ∈ I' n, g u ≠ 0 → (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs) → (I' n ∩ Function.support g).Finite := by
    intro n g hg
    refine (Set.Finite.biUnion (Set.finite_univ : (Set.univ : Set ↥hBfinS.toFinset).Finite) fun β _ =>
      ((hboxfin (R₀ + ∑ i, |(Log (ubS β)).1 i|) (fun j => -((f (T.equivFin.symm j).1 : ℤ) * n j) - (Log (ubS β)).2 j)).image
        fun a => ubS β * a)).subset ?_
    rintro u ⟨huI, hu⟩
    have huQ := (hg u huI hu).2
    refine Set.mem_biUnion (Set.mem_univ (⟨pat u, hβ_ofS u huQ⟩ : ↥hBfinS.toFinset)) ⟨(ubS ⟨pat u, hβ_ofS u huQ⟩)⁻¹ * u, ⟨?_, ?_, ?_⟩, by group⟩
    · exact ((hA_mem _).1 (hdivAS u huQ)).1
    · intro i
      rw [hLog_mul, hLog_inv, Prod.fst_add, Prod.fst_neg, Pi.add_apply, Pi.neg_apply]
      have h1 := (hg u huI hu).1 i
      have h2 : |(Log (ubS ⟨pat u, hβ_ofS u huQ⟩)).1 i| ≤ ∑ i, |(Log (ubS ⟨pat u, hβ_ofS u huQ⟩)).1 i| :=
        Finset.single_le_sum (f := fun i => |(Log (ubS ⟨pat u, hβ_ofS u huQ⟩)).1 i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      calc |-(Log (ubS ⟨pat u, hβ_ofS u huQ⟩)).1 i + (Log u).1 i|
          ≤ |-(Log (ubS ⟨pat u, hβ_ofS u huQ⟩)).1 i| + |(Log u).1 i| := abs_add_le _ _
        _ ≤ _ := by rw [abs_neg]; linarith
    · funext j
      rw [hLog_mul, hLog_inv, Prod.snd_add, Prod.snd_neg, Pi.add_apply, Pi.neg_apply, ((hI'_val n u).1 huI).2 j]
      ring

  have hpat_mulA : ∀ (u a : Kˣ), a ∈ A → pat (u * a) = pat u := by
    intro u a ha
    funext v
    rw [hpat, hpat, map_mul, ((hA_mem a).1 ha).1 v.1 (hST v.1 v.2), mul_one]
  have hsplitG : ∀ (n : Fin T.card → ℤ) (g : Kˣ → ℂ),
      (∀ u ∈ I' n, g u ≠ 0 → (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs) →
      ∑ᶠ u ∈ I' n, g u = ∑ β : ↥hBfinS.toFinset, ∑ z ∈ hμfin.toFinset, ∑ j : Fin nCs,
        ∑ᶠ h ∈ (Hs : Set Kˣ), (if ubS β * (z * cCs j * h) ∈ I' n then g (ubS β * (z * cCs j * h)) else 0) := by
    intro n g hg
    have hSfin := hSfinG n g hg
    have hI'Q : ∀ u ∈ I' n, g u ≠ 0 → u ∈ Qs := fun u hu hne => (hg u hu hne).2
    let gβ : ↥hBfinS.toFinset → Kˣ → ℂ := fun β a => if ubS β * a ∈ I' n then g (ubS β * a) else 0
    have hsplit : ∑ᶠ u ∈ I' n, g u = ∑ β : ↥hBfinS.toFinset, ∑ᶠ a ∈ (A : Set Kˣ), gβ β a := by
      let Sβ : ↥hBfinS.toFinset → Set Kˣ := fun β =>
        (I' n ∩ (fun a => ubS β * a) '' (A : Set Kˣ)) ∩ Function.support g
      have hSβfin : ∀ β, (Sβ β).Finite := fun β =>
        hSfin.subset (Set.inter_subset_inter_left _ Set.inter_subset_left)
      have hSβdisj : Pairwise (fun β β' => Disjoint (Sβ β) (Sβ β')) := by
        intro β β' hne
        refine Set.disjoint_left.2 fun u hu hu' => hne ?_
        obtain ⟨a, ha, hua⟩ := hu.1.2
        obtain ⟨a', ha', hua'⟩ := hu'.1.2
        have hua₁ : ubS β * a = u := hua
        have hua₂ : ubS β' * a' = u := hua'
        apply Subtype.ext
        rw [← hubpatS β, ← hubpatS β', ← hpat_mulA (ubS β) a ha, ← hpat_mulA (ubS β') a' ha', hua₁, hua₂]
      have hUn : I' n ∩ Function.support g = ⋃ β, Sβ β := by
        ext u
        constructor
        · rintro ⟨huI, hu⟩
          have huQ := hI'Q u huI hu
          exact Set.mem_iUnion.2 ⟨⟨pat u, hβ_ofS u huQ⟩,
            ⟨huI, (ubS ⟨pat u, hβ_ofS u huQ⟩)⁻¹ * u, hdivAS u huQ, mul_inv_cancel_left _ _⟩, hu⟩
        · intro h
          obtain ⟨β, hβ⟩ := Set.mem_iUnion.1 h
          exact ⟨hβ.1.1, hβ.2⟩
      calc ∑ᶠ u ∈ I' n, g u = ∑ᶠ u ∈ I' n ∩ Function.support g, g u :=
            (finsum_mem_inter_support _ _).symm
        _ = ∑ᶠ u ∈ ⋃ β, Sβ β, g u := by rw [hUn]
        _ = ∑ᶠ β, ∑ᶠ u ∈ Sβ β, g u := finsum_mem_iUnion hSβdisj hSβfin
        _ = ∑ β, ∑ᶠ u ∈ Sβ β, g u := finsum_eq_sum_of_fintype _
        _ = ∑ β, ∑ᶠ a ∈ (A : Set Kˣ), gβ β a := Finset.sum_congr rfl fun β _ => ?_
      have hbij : Set.BijOn (fun a => ubS β * a) ((A : Set Kˣ) ∩ {a | ubS β * a ∈ I' n})
          (I' n ∩ (fun a => ubS β * a) '' (A : Set Kˣ)) := by
        refine ⟨fun a ha => ⟨ha.2, a, ha.1, rfl⟩, (mul_right_injective (ubS β)).injOn, ?_⟩
        rintro u ⟨huI, a, ha, rfl⟩
        exact ⟨a, ⟨ha, huI⟩, rfl⟩
      calc ∑ᶠ u ∈ Sβ β, g u = ∑ᶠ u ∈ I' n ∩ (fun a => ubS β * a) '' (A : Set Kˣ), g u :=
            finsum_mem_inter_support _ _
        _ = ∑ᶠ a ∈ (A : Set Kˣ) ∩ {a | ubS β * a ∈ I' n}, g (ubS β * a) :=
            (finsum_mem_eq_of_bijOn _ hbij (fun a _ => rfl)).symm
        _ = ∑ᶠ a ∈ (A : Set Kˣ), gβ β a := (NumCore.finsum_mem_ite _ _ _).symm
    have hICβ : ∀ β : ↥hBfinS.toFinset, ∑ᶠ a ∈ (A : Set Kˣ), gβ β a =
        ∑ z ∈ hμfin.toFinset, ∑ j : Fin nCs, ∑ᶠ h ∈ (Hs : Set Kˣ), gβ β (z * cCs j * h) := by
      intro β
      refine hICsℂ (gβ β) ?_
      refine ((hSfin.preimage ((mul_right_injective (ubS β)).injOn)).subset ?_)
      rintro a ⟨-, hga⟩
      rw [Function.mem_support] at hga
      by_cases h : ubS β * a ∈ I' n
      · refine ⟨h, ?_⟩
        rw [Function.mem_support]
        simpa [gβ, h] using hga
      · exact absurd (by simp [gβ, h]) hga
    rw [hsplit]
    exact Finset.sum_congr rfl fun β _ => hICβ β

  let I₀ := ↥hBfinS.toFinset × ↥hμfin.toFinset × Fin nCs
  let urep : I₀ → Kˣ := fun i => ubS i.1 * ((i.2.1 : Kˣ) * cCs i.2.2)
  let n₀f : Kˣ → Fin T.card → ℤ := fun u j => -((Log u).2 j / (f (T.equivFin.symm j).1 : ℤ))
  have hurep_T : ∀ (i : I₀) (v : HeightOneSpectrum (𝓞 K)), v ∉ SK → v ∉ T → v.valuationOfNeZero (urep i) = 1 := by
    intro i v hvS hvT
    have hz : (i.2.1 : Kˣ) ∈ A := hμA ((hμfin.mem_toFinset).1 i.2.1.2)
    simp only [urep]
    rw [map_mul, map_mul, (hubQS i.1).1 v hvS hvT, ((hA_mem _).1 hz).1 v hvT, ((hA_mem _).1 (hcAs i.2.2)).1 v hvT, one_mul, one_mul]
  have hurep_dvd : ∀ (i : I₀) (j' : Fin T.card), (f (T.equivFin.symm j').1 : ℤ) ∣ (Log (urep i)).2 j' := by
    intro i j'
    have hz : (i.2.1 : Kˣ) ∈ A := hμA ((hμfin.mem_toFinset).1 i.2.1.2)
    simp only [urep]
    rw [hLog_mul, hLog_mul, Prod.snd_add, Prod.snd_add, Pi.add_apply, Pi.add_apply]
    refine dvd_add ?_ (dvd_add (hfdvd _ hz j') (hfdvd _ (hcAs i.2.2) j'))
    rw [hLog2]
    exact (hubQS i.1).2.1 _ (T.equivFin.symm j').2

  let uv : Kˣ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun u v =>
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u
  have huv : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)), ((uv u v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = bS u v := by
    intro u v
    rw [hbS]
    simp only [uv, Units.coe_map, MonoidHom.coe_coe, NumCore.algebraMap_adicCompletion_apply]
  have huv_mul : ∀ (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K)), uv (a * b) v = uv a v * uv b v := fun a b v => by
    simp only [uv, map_mul]

  have hWd : ∀ (v : HeightOneSpectrum (𝓞 K)) (α b₀ : (v.adicCompletion K)ˣ),
      ∃ Φd : (v.adicCompletion K) × (v.adicCompletion K) → ℂ, v ∈ SK →
      (IsLocallyConstant Φd ∧ HasCompactSupport Φd ∧ (∀ p, Φd p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) ∧
      ∀ b z : (v.adicCompletion K)ˣ, Φd ((b : v.adicCompletion K), (z : v.adicCompletion K)) =
        if (z * b)⁻¹ * α ∈ Av v ∧ b * b₀⁻¹ ∈ Av v then 1 else 0) := by
    intro v
    rcases em (v ∈ SK) with hv | hv
    · intro α b₀
      obtain ⟨-, -, -, hAo, hAc, -⟩ := hDSv v hv
      let I : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ := fun p =>
        if (p.2 * p.1)⁻¹ * α ∈ Av v ∧ p.1 * b₀⁻¹ ∈ Av v then 1 else 0
      have hI : IsLocallyConstant I ∧ HasCompactSupport I ∧ ∀ (b z σ : (v.adicCompletion K)ˣ), σ ∈ Av v → I (b * σ, z) = I (b, z) :=
        NumdDefect.cellIndicator_isLocallyConstant_hasCompactSupport_invariant (Av v) (Av v) hAo hAc hAo le_rfl α b₀⁻¹
      obtain ⟨Φd, h1, h2, h3, h4⟩ := NumCore.zeroExt K v I hI.1 hI.2.1
      exact ⟨Φd, fun _ => ⟨h1, h2, h3, fun b z => h4 b z⟩⟩
    · intro α b₀
      exact ⟨0, fun h => absurd h hv⟩
  choose Φd hΦd using hWd
  let ΦFd : ∀ (v : HeightOneSpectrum (𝓞 K)) (α b₀ : (v.adicCompletion K)ˣ),
      (∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ) :=
    fun v α b₀ => Function.update Φf v (Φd v α b₀)
  have hΦFd : ∀ v ∈ SK, ∀ (α b₀ : (v.adicCompletion K)ˣ), ∀ v' ∈ SK,
      IsLocallyConstant (ΦFd v α b₀ v') ∧ HasCompactSupport (ΦFd v α b₀ v') ∧ ∀ p, ΦFd v α b₀ v' p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    intro v hv α b₀ v' hv'
    by_cases h : v' = v
    · subst h
      simp only [ΦFd, Function.update_self]
      exact ⟨(hΦd v' α b₀ hv).1, (hΦd v' α b₀ hv).2.1, (hΦd v' α b₀ hv).2.2.1⟩
    · simp only [ΦFd, Function.update_of_ne h]
      exact hΦf v' hv'

  let Shc := Σ v : ↥SK, ↥(Fa v.1)

  let WB : I₀ → mixedEmbedding.mixedSpace K → ℂ := fun i y => C * (c' * ∑ ξ : ↥Ξ, Bt ξ y (bS (urep i)))
  let WC : I₀ → InfinitePlace K → mixedEmbedding.mixedSpace K → ℂ := fun i w y => C * (c' * ∑ ξ : ↥Ξ, Ct ξ w y (bS (urep i)))
  let WE : I₀ → InfinitePlace K → mixedEmbedding.mixedSpace K → ℂ := fun i w y => C * (c' * ∑ ξ : ↥Ξ, Et ξ w y (bS (urep i)))
  let W0 : I₀ → ↥SK → mixedEmbedding.mixedSpace K → ℂ := fun i v y => C * (c' * ∑ ξ : ↥Ξ, Wf ξ (ΦF0 v.1) y (bS (urep i)))
  let Wc : I₀ → Shc → mixedEmbedding.mixedSpace K → ℂ := fun i p y =>
    C * (c' * ∑ ξ : ↥Ξ, Wf ξ (ΦFd p.1.1 p.2.1 (uv (urep i) p.1.1)) y (bS (urep i)))
  have hWB_sm : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (WB i) := fun i =>
    contDiff_const.mul (contDiff_const.mul (ContDiff.sum fun ξ _ => (hBCE_smooth ξ (bS (urep i))).1))
  have hWC_sm : ∀ i w, ContDiff ℝ (⊤ : ℕ∞) (WC i w) := fun i w =>
    contDiff_const.mul (contDiff_const.mul (ContDiff.sum fun ξ _ => ((hBCE_smooth ξ (bS (urep i))).2 w).1))
  have hWE_sm : ∀ i w, ContDiff ℝ (⊤ : ℕ∞) (WE i w) := fun i w =>
    contDiff_const.mul (contDiff_const.mul (ContDiff.sum fun ξ _ => ((hBCE_smooth ξ (bS (urep i))).2 w).2))
  have hW0_sm : ∀ i v, ContDiff ℝ (⊤ : ℕ∞) (W0 i v) := fun i v =>
    contDiff_const.mul (contDiff_const.mul (ContDiff.sum fun ξ _ => (hK7 ξ (ΦF0 v.1) (hΦF0 v.1 v.2) (bS (urep i))).2))
  have hWc_sm : ∀ i p, ContDiff ℝ (⊤ : ℕ∞) (Wc i p) := fun i p =>
    contDiff_const.mul (contDiff_const.mul (ContDiff.sum fun ξ _ =>
      (hK7 ξ (ΦFd p.1.1 p.2.1 (uv (urep i) p.1.1)) (hΦFd p.1.1 p.1.2 p.2.1 (uv (urep i) p.1.1)) (bS (urep i))).2))
  have hWB0 : ∀ i y, WB i y ≠ 0 → y ∈ Call := by
    intro i y hy
    by_contra hc
    apply hy
    have : ∀ ξ : ↥Ξ, Bt ξ y (bS (urep i)) = 0 := fun ξ =>
      ((hC₁ ξ).2.2 y (bS (urep i)) (fun h => hc (Or.inr (Set.mem_iUnion.2 ⟨ξ, h⟩)))).1
    simp only [WB, this, Finset.sum_const_zero, mul_zero]
  have hWC0 : ∀ i w y, WC i w y ≠ 0 → y ∈ Call := by
    intro i w y hy
    by_contra hc
    apply hy
    have : ∀ ξ : ↥Ξ, Ct ξ w y (bS (urep i)) = 0 := fun ξ =>
      (((hC₁ ξ).2.2 y (bS (urep i)) (fun h => hc (Or.inr (Set.mem_iUnion.2 ⟨ξ, h⟩)))).2 w).1
    simp only [WC, this, Finset.sum_const_zero, mul_zero]
  have hWE0 : ∀ i w y, WE i w y ≠ 0 → y ∈ Call := by
    intro i w y hy
    by_contra hc
    apply hy
    have : ∀ ξ : ↥Ξ, Et ξ w y (bS (urep i)) = 0 := fun ξ =>
      (((hC₁ ξ).2.2 y (bS (urep i)) (fun h => hc (Or.inr (Set.mem_iUnion.2 ⟨ξ, h⟩)))).2 w).2
    simp only [WE, this, Finset.sum_const_zero, mul_zero]
  have hW00 : ∀ i v y, W0 i v y ≠ 0 → y ∈ Call := by
    intro i v y hy
    by_contra hc
    apply hy
    have : ∀ ξ : ↥Ξ, Wf ξ (ΦF0 v.1) y (bS (urep i)) = 0 := fun ξ => by
      by_contra h; exact hc (Or.inl (hWf0 ξ _ y _ h))
    simp only [W0, this, Finset.sum_const_zero, mul_zero]
  have hWc0 : ∀ i p y, Wc i p y ≠ 0 → y ∈ Call := by
    intro i p y hy
    by_contra hc
    apply hy
    have : ∀ ξ : ↥Ξ, Wf ξ (ΦFd p.1.1 p.2.1 (uv (urep i) p.1.1)) y (bS (urep i)) = 0 := fun ξ => by
      by_contra h; exact hc (Or.inl (hWf0 ξ _ y _ h))
    simp only [Wc, this, Finset.sum_const_zero, mul_zero]

  have hP_bddC : ∀ σ (C₂ : Set (mixedEmbedding.mixedSpace K)), IsCompact C₂ → (∀ y ∈ C₂, IsUnit y) →
      ∃ R : ℝ, ∀ (x : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)
        (θ : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → ℝ), P σ (x, θ) ∈ C₂ → ∀ i, |x i| ≤ R :=
    fun σ C₂ hC hu => (hP_bdd C₂ hC hu).imp fun R hR x θ => hR σ x θ

  have hTW0 : ∀ (i : I₀) (v : ↥SK), ∃ (G : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
      (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Rb : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) G ∧ 0 ≤ Rb ∧
      (∀ p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
          (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ), (∃ i, Rb < |p.1 i|) → G p = 0) ∧
      (∀ (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
          (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))
          (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)), G (p.1, p.2 + Pi.single J 1) = G p) ∧
      ∀ (x : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)
        (θ : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → ℝ) (k : Fin T.card → ℤ)
        (Θ : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (tvec j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖tvec j‖ ^ (-(k j)) →
        G ((Log (urep i)).1 + x, Θ) = (∏ j, tvec j ^ (-(n₀f (urep i) j + k j))) *
          W0 i v (P (sgn (emb (urep i))) ((Log (urep i)).1, 0) * P 1 (x, θ)) := by
    intro i v
    obtain ⟨G, hG, ⟨Rb, hRb, hsupp⟩, hper, hid⟩ :=
      NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
        K (P (sgn (emb (urep i)))) (P 1) (hP_smooth _) (hP_per _) (hP_mul' _) (hP_bddC _)
        (W0 i v) (hW0_sm i v) Call hCall hCallu (hW00 i v) cs ts tvec htvec ℓ
        (Log (urep i)).1 0 (n₀f (urep i))
    exact ⟨G, Rb, hG, hRb, hsupp, hper, hid⟩
  choose G0 Rb0 hG0_sm hRb0 hG0_supp hG0_per hG0_id using hTW0
  have hTWc : ∀ (i : I₀) (p : Shc), ∃ (G : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
      (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ) (Rb : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) G ∧ 0 ≤ Rb ∧
      (∀ p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
          (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ), (∃ i, Rb < |p.1 i|) → G p = 0) ∧
      (∀ (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
          (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))
          (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)), G (p.1, p.2 + Pi.single J 1) = G p) ∧
      ∀ (x : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)
        (θ : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → ℝ) (k : Fin T.card → ℤ)
        (Θ : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (tvec j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖tvec j‖ ^ (-(k j)) →
        G ((Log (urep i)).1 + x, Θ) = (∏ j, tvec j ^ (-(n₀f (urep i) j + k j))) *
          Wc i p (P (sgn (emb (urep i))) ((Log (urep i)).1, 0) * P 1 (x, θ)) := by
    intro i p
    obtain ⟨G, hG, ⟨Rb, hRb, hsupp⟩, hper, hid⟩ :=
      NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
        K (P (sgn (emb (urep i)))) (P 1) (hP_smooth _) (hP_per _) (hP_mul' _) (hP_bddC _)
        (Wc i p) (hWc_sm i p) Call hCall hCallu (hWc0 i p) cs ts tvec htvec ℓ
        (Log (urep i)).1 0 (n₀f (urep i))
    exact ⟨G, Rb, hG, hRb, hsupp, hper, hid⟩
  choose Gc Rbc hGc_sm hRbc hGc_supp hGc_per hGc_id using hTWc

  let ιw : InfinitePlace K → Fin (Fintype.card (NumberField.InfinitePlace K)) := Fintype.equivFin (NumberField.InfinitePlace K)
  let cw : {w : InfinitePlace K // w.IsComplex} → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) :=
    fun w => Fin.castAdd T.card (ιw w.1)
  have hcw : Function.Injective cw := by
    intro a b h
    have h1 : ιw a.1 = ιw b.1 := Fin.castAdd_injective _ _ h
    exact Subtype.ext ((Fintype.equivFin (NumberField.InfinitePlace K)).injective h1)
  have hcs_cw : ∀ j, cs j = cw ((Fintype.equivFin {w : NumberField.InfinitePlace K // w.IsComplex}).symm j) := fun j => rfl
  let wR : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}) ≃ {w : InfinitePlace K // w.IsReal} :=
    (Fintype.equivFin {w : InfinitePlace K // w.IsReal}).symm
  let kR : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}) → Fin (Fintype.card (NumberField.InfinitePlace K)) :=
    fun k => ιw (wR k).1
  let kC : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → Fin (Fintype.card (NumberField.InfinitePlace K)) :=
    fun j => if h : ∃ w : {w : InfinitePlace K // w.IsComplex}, cw w = j then ιw h.choose.1 else ⟨0, hr0⟩
  have hkC : ∀ w : {w : InfinitePlace K // w.IsComplex}, kC (cw w) = ιw w.1 := by
    intro w
    have h : ∃ w' : {w : InfinitePlace K // w.IsComplex}, cw w' = cw w := ⟨w, rfl⟩
    simp only [kC, dif_pos h]
    rw [hcw h.choose_spec]

  have hKW : ∀ i : I₀, ∃ (Bw : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
        (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ)
      (Cw : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}) → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
        (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ)
      (Ew : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
        (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ),
      (ContDiff ℝ (⊤ : ℕ∞) Bw ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Cw k)) ∧ ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Ew j)) ∧
      (∀ (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))
        (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
        Bw (p.1, p.2 + Pi.single J 1) = Bw p ∧ (∀ k, Cw k (p.1, p.2 + Pi.single J 1) = Cw k p) ∧
          ∀ j, Ew j (p.1, p.2 + Pi.single J 1) = Ew j p) ∧
      (∃ Rb : ℝ, 0 ≤ Rb ∧ ∀ p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
        (∃ i, Rb < |p.1 i|) → Bw p = 0 ∧ (∀ k, Cw k p = 0) ∧ ∀ j, Ew j p = 0) ∧
      ∀ (x : Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (θ : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → ℝ)
        (k : Fin T.card → ℤ) (Θ : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (tvec j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖tvec j‖ ^ (-(k j)) →
        Bw ((Log (urep i)).1 + x, Θ) +
            ∑ k' : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}), ((|1 - Real.exp (((Log (urep i)).1 + x) (kR k'))| : ℝ) : ℂ) * Cw k' ((Log (urep i)).1 + x, Θ) +
            ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card),
              ((‖(1 : ℂ) - Complex.exp (((((Log (urep i)).1 + x) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ j : ℝ) : ℂ))‖ ^ 2 *
                Real.log ‖(1 : ℂ) - Complex.exp (((((Log (urep i)).1 + x) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
              Ew j ((Log (urep i)).1 + x, Θ) =
          (∏ j, tvec j ^ (-(n₀f (urep i) j + k j))) *
            (WB i (P (sgn (emb (urep i))) ((Log (urep i)).1, 0) * P 1 (x, θ)) +
              ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal),
                ((if hw : w.IsReal then
                    (if sgn (emb (urep i)) ⟨w, hw⟩ = 1 then
                        Real.exp (-(((Log (urep i)).1 + x) (ιw w))) * |1 - Real.exp (((Log (urep i)).1 + x) (ιw w))|
                      else 1 + Real.exp (-(((Log (urep i)).1 + x) (ιw w))))
                  else 0 : ℝ) : ℂ) * WC i w (P (sgn (emb (urep i))) ((Log (urep i)).1, 0) * P 1 (x, θ)) +
              ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                ((if hw : w.IsComplex then
                    Real.exp (-(((Log (urep i)).1 + x) (ιw w))) *
                      (‖(1 : ℂ) - Complex.exp (((((Log (urep i)).1 + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2 *
                          Real.log ‖(1 : ℂ) - Complex.exp (((((Log (urep i)).1 + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ -
                        ((Log (urep i)).1 + x) (ιw w) / 2 *
                          ‖(1 : ℂ) - Complex.exp (((((Log (urep i)).1 + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2)
                  else 0 : ℝ) : ℂ) * WE i w (P (sgn (emb (urep i))) ((Log (urep i)).1, 0) * P 1 (x, θ))) :=
    fun i =>
      NumberField.mixedEmbedding.exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord
        K (P (sgn (emb (urep i)))) (P 1) (hP_smooth _) (hP_per _) (hP_mul' _) (hP_bddC _)
        Call hCall hCallu cs ts tvec htvec ℓ (Log (urep i)).1 (n₀f (urep i)) ιw (sgn (emb (urep i))) cw hcw
        wR kR (fun _ => rfl) kC hkC (WB i) (hWB_sm i) (hWB0 i) (WC i) (hWC_sm i) (hWC0 i) (WE i) (hWE_sm i) (hWE0 i)
  choose BwA CwA EwA hA_sm hA_per hA_box hA_id using hKW
  choose RbA hRbA hA_supp using hA_box

  choose SL hSL using hLS

  have hper_int : ∀ (G : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ), (∀ (p : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))) (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
        G (p.1, p.2 + Pi.single J 1) = G p) →
      ∀ (x : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)) (Θ : (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (m : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℤ),
        G (x, Θ + fun J => (m J : ℝ)) = G (x, Θ) := by
    intro G hG x
    have h0 : ∀ (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)) (m : ℕ) (Θ : (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        G (x, Θ + (m : ℝ) • Pi.single J (1 : ℝ)) = G (x, Θ) := by
      intro J m
      induction m with
      | zero => intro Θ; simp
      | succ m ih =>
        intro Θ
        have := hG (x, Θ + (m : ℝ) • Pi.single J (1 : ℝ)) J
        simp only at this
        rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc, this, ih]
    have h1 : ∀ (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)) (m : ℤ) (Θ : (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        G (x, Θ + (m : ℝ) • Pi.single J (1 : ℝ)) = G (x, Θ) := by
      intro J m Θ
      rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
      · rw [Int.cast_natCast]; exact h0 J k Θ
      · have := h0 J k (Θ + ((-(k : ℤ) : ℤ) : ℝ) • Pi.single J (1 : ℝ))
        rw [add_assoc, ← add_smul] at this
        simp only [Int.cast_neg, Int.cast_natCast, neg_add_cancel, zero_smul, add_zero] at this
        rw [Int.cast_neg, Int.cast_natCast]
        exact this.symm
    intro Θ m
    have hm : (fun J => (m J : ℝ)) = ∑ J, (m J : ℝ) • Pi.single J (1 : ℝ) := by
      ext J'
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    rw [hm]
    have : ∀ s : Finset (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
        G (x, Θ + ∑ J ∈ s, (m J : ℝ) • Pi.single J (1 : ℝ)) = G (x, Θ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert J s hJ ih => rw [Finset.sum_insert hJ, add_comm ((m J : ℝ) • _), ← add_assoc, h1, ih]
    exact this Finset.univ
  have hmul_eq_one_iff : ∀ (u g : Kˣ), ((u * g : Kˣ) : K) = 1 ↔ g = u⁻¹ := by
    intro u g
    rw [← Units.val_one, Units.val_inj, mul_eq_one_iff_eq_inv']
  have hTYPE : ∀ (n : Fin T.card → ℤ) (H' : Subgroup Kˣ) (hH' : H' ≤ FA) (u : Kˣ) (piece : Kˣ → ℂ)
      (Kf : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ) (Rb : ℝ), (∀ p : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), (∃ i, Rb < |p.1 i|) → Kf p = 0) →
      ∀ (lam : ℂ) (x₀ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)) (θ₀ : (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (n₀ : (Fin T.card → ℤ)),
      (∀ g ∈ H', ((u * g : Kˣ) : K) ≠ 1 → C * (if u * g ∈ I' n then piece (u * g) else 0) =
          lam * (if (Lmap g).2 + n₀ = n then Kf (x₀ + (Lmap g).1, θ₀ + lift (Lmap g)) else 0)) →
      ∑ᶠ g ∈ (H' : Set Kˣ), C * (if u * g ∈ I' n ∧ ((u * g : Kˣ) : K) ≠ 1 then piece (u * g) else 0) =
        lam * ∑' γ : SL H' hH', (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ = n then
            Kf (x₀ + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0) +
        (-(lam * @ite ℂ (u⁻¹ ∈ H') (Classical.dec _) 1 0)) * ∑' γ : (⊥ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))),
          (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + (n₀ + (Lmap u⁻¹).2) = n then
            Kf ((x₀ + (Lmap u⁻¹).1) + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, (θ₀ + lift (Lmap u⁻¹)) + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0) := by
    intro n H' hH' u piece Kf Rb hKb lam x₀ θ₀ n₀ hpt
    let Ψ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → ℂ := fun γ => lam * (if γ.2 + n₀ = n then Kf (x₀ + γ.1, θ₀ + lift γ) else 0)
    let F : Kˣ → ℂ := fun g => C * (if u * g ∈ I' n ∧ ((u * g : Kˣ) : K) ≠ 1 then piece (u * g) else 0)

    have hΨfin : (Function.support Ψ ∩ (SL H' hH' : Set _)).Finite := by
      haveI := hΛ_disc
      have hF := AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology Λ (Rb + ∑ i, |x₀ i|) (n - n₀)
      refine hF.subset ?_
      rintro γ ⟨hγ, hγS⟩
      rw [Function.mem_support] at hγ
      by_cases hc : γ.2 + n₀ = n
      · refine ⟨(hSL H' hH').1 hγS, fun i => ?_, by rw [← hc]; simp⟩
        by_contra hlt
        push_neg at hlt
        apply hγ
        simp only [Ψ, if_pos hc]
        rw [hKb _ ⟨i, ?_⟩, mul_zero]
        simp only [Pi.add_apply]
        have h2 : |x₀ i| ≤ ∑ i, |x₀ i| := Finset.single_le_sum (f := fun i => |x₀ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
        have h3 : |γ.1 i| ≤ |x₀ i + γ.1 i| + |x₀ i| := by
          have := abs_sub (x₀ i + γ.1 i) (x₀ i)
          simp only [add_sub_cancel_left] at this
          linarith
        linarith
      · exact absurd (show Ψ γ = 0 by simp only [Ψ, if_neg hc, mul_zero]) hγ
    have hΨL : (↑H' ∩ Function.support fun g => Ψ (Lmap g)).Finite := by
      have hinj : Set.InjOn Lmap (H' : Set Kˣ) := by
        intro a ha b hb hab
        have h0 : Lmap (a * b⁻¹) = 0 := by
          rw [hL_add a (hH' ha) b⁻¹ (FA.inv_mem (hH' hb)), hL_inv b (hH' hb), hab, add_neg_cancel]
        have := hL_inj _ (FA.mul_mem (hH' ha) (FA.inv_mem (hH' hb))) h0
        rw [mul_inv_eq_one] at this
        exact this
      refine Set.Finite.of_finite_image ?_ (hinj.mono Set.inter_subset_left)
      refine hΨfin.subset ?_
      rintro _ ⟨g, ⟨hg, hgs⟩, rfl⟩
      exact ⟨hgs, ((hSL H' hH').2.1 _).2 ⟨g, hg, rfl⟩⟩

    have hpoint : ∀ g ∈ (H' : Set Kˣ), Ψ (Lmap g) = F g + (if g = u⁻¹ then Ψ (Lmap g) else 0) := by
      intro g hg
      by_cases h1 : g = u⁻¹
      · have : ¬ (u * g ∈ I' n ∧ ((u * g : Kˣ) : K) ≠ 1) := fun h => h.2 ((hmul_eq_one_iff u g).2 h1)
        simp only [F, if_neg this, if_pos h1, mul_zero, zero_add]
      · have hne : ((u * g : Kˣ) : K) ≠ 1 := fun h => h1 ((hmul_eq_one_iff u g).1 h)
        have := hpt g hg hne
        simp only [F, Ψ, if_neg h1, add_zero]
        rw [← this]
        by_cases hI : u * g ∈ I' n
        · rw [if_pos hI, if_pos ⟨hI, hne⟩]
        · rw [if_neg hI, if_neg (fun h => hI h.1)]
    have hFfin : (↑H' ∩ Function.support F).Finite := by
      refine (hΨL.union (Set.finite_singleton u⁻¹)).subset ?_
      rintro g ⟨hg, hFg⟩
      by_cases h1 : g = u⁻¹
      · exact Or.inr h1
      · left
        refine ⟨hg, ?_⟩
        rw [Function.mem_support] at hFg ⊢
        rw [hpoint g hg, if_neg h1, add_zero]
        exact hFg
    have hGfin : (↑H' ∩ Function.support fun g => if g = u⁻¹ then Ψ (Lmap g) else 0).Finite := by
      refine (Set.finite_singleton u⁻¹).subset ?_
      rintro g ⟨-, hg⟩
      rw [Function.mem_support] at hg
      by_contra h
      exact hg (if_neg h)
    have hsum : ∑ᶠ g ∈ (H' : Set Kˣ), Ψ (Lmap g) = ∑ᶠ g ∈ (H' : Set Kˣ), F g +
        ∑ᶠ g ∈ (H' : Set Kˣ), (if g = u⁻¹ then Ψ (Lmap g) else 0) := by
      rw [← finsum_mem_add_distrib' hFfin hGfin]
      exact finsum_mem_congr rfl hpoint
    have hghost : ∑ᶠ g ∈ (H' : Set Kˣ), (if g = u⁻¹ then Ψ (Lmap g) else 0) = (@ite ℂ (u⁻¹ ∈ H') (Classical.dec _) 1 0) * Ψ (Lmap u⁻¹) := by
      rw [NumCore.finsum_mem_ite]
      by_cases hu : u⁻¹ ∈ H'
      · have : (H' : Set Kˣ) ∩ {g | g = u⁻¹} = {u⁻¹} := by
          ext g
          simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_setOf_eq, Set.mem_singleton_iff]
          exact ⟨fun h => h.2, fun h => ⟨h ▸ hu, h⟩⟩
        rw [this, finsum_mem_singleton, if_pos hu, one_mul]
      · have : (H' : Set Kˣ) ∩ {g | g = u⁻¹} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun g hg => hu ?_
          have h2 : g = u⁻¹ := hg.2
          exact h2 ▸ hg.1
        rw [this, finsum_mem_empty, if_neg hu, zero_mul]
    have hmain : ∑ᶠ g ∈ (H' : Set Kˣ), Ψ (Lmap g) = ∑' γ : SL H' hH', Ψ (γ : _) := (hSL H' hH').2.2 Ψ hΨfin
    have hbot : ∑' γ : (⊥ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))),
          (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + (n₀ + (Lmap u⁻¹).2) = n then
            Kf ((x₀ + (Lmap u⁻¹).1) + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, (θ₀ + lift (Lmap u⁻¹)) + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0) =
        (if (Lmap u⁻¹).2 + n₀ = n then Kf (x₀ + (Lmap u⁻¹).1, θ₀ + lift (Lmap u⁻¹)) else 0) := by
      rw [tsum_eq_single (⟨0, (⊥ : AddSubgroup _).zero_mem⟩ : ↥(⊥ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))))
        (fun b' hb' => absurd (Subsingleton.elim b' _) hb')]
      simp only [Prod.snd_zero, Prod.fst_zero, zero_add, add_zero, hlift0]
      rw [add_comm n₀]
    show ∑ᶠ g ∈ (H' : Set Kˣ), F g = _
    rw [hbot]
    have hΨmul : ∑' γ : SL H' hH', Ψ (γ : _) = lam * ∑' γ : SL H' hH', (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ = n then
        Kf (x₀ + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0) := by
      simp only [Ψ]
      exact tsum_mul_left
    have key : ∑ᶠ g ∈ (H' : Set Kˣ), F g = ∑' γ : SL H' hH', Ψ (γ : _) - (@ite ℂ (u⁻¹ ∈ H') (Classical.dec _) 1 0) * Ψ (Lmap u⁻¹) := by
      rw [← hmain, hsum, hghost]; ring
    rw [key, hΨmul]
    simp only [Ψ]
    ring

  have hnorm_one : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K), Valued.v x = 1 → ‖x‖ = 1 := by
    intro v x h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.2 h.le
    · exact Valued.toNormedField.one_le_norm_iff.2 h.ge
  have hnormA : ∀ g ∈ A, ∀ v ∈ SK, ‖bS g v‖ = 1 := by
    intro g hg v hv
    rw [hbS]
    apply hnorm_one
    have h1 : v.valuationOfNeZero g = 1 := ((hA_mem g).1 hg).1 v (hST v hv)
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq, h1]
    rfl
  have hLmap1 : ∀ g : Kˣ, (Lmap g).1 = (Log g).1 := fun g => rfl
  have hbS_mul : ∀ (a b : Kˣ) (v : HeightOneSpectrum (𝓞 K)), bS (a * b) v = bS a v * bS b v := by
    intro a b v
    simp only [bS, map_mul, Units.val_mul]
    rfl
  have hsqrtA : ∀ (u : Kˣ), ∀ g ∈ Hs, ∀ v ∈ SK, Real.sqrt ‖bS (u * g) v‖ = Real.sqrt ‖bS u v‖ := by
    intro u g hg v hv
    rw [hbS_mul, norm_mul, hnormA g (hHsA hg) v hv, mul_one]
  have huvφ : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)),
      Units.map (AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom (ιK u) = uv u v := by
    intro u v
    ext
    rw [hφv, huv]
  have huv_Us : ∀ g ∈ Hs, ∀ v ∈ SK, uv g v ∈ Us v := fun g hg v hv => ((hHs_mem g).1 hg).2.2.1 v hv

  have hprodInv : ∀ (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ),
      (∀ v' ∈ SK, ∀ t ∈ Us v', ∀ b z : v'.adicCompletion K, F v' (b * (t : v'.adicCompletion K), z) = F v' (b, z)) →
      ∀ g ∈ Hs, ∀ (u : Kˣ) (z : (v' : HeightOneSpectrum (𝓞 K)) → v'.adicCompletion K),
        ∏ v' ∈ SK, F v' (bS (u * g) v', z v') = ∏ v' ∈ SK, F v' (bS u v', z v') := by
    intro F hF g hg u z
    refine Finset.prod_congr rfl fun v' hv' => ?_
    rw [hbS_mul, ← huv g v']
    exact hF v' hv' _ (huv_Us g hg v' hv') _ _
  have hΦf_inv : ∀ v' ∈ SK, ∀ t ∈ Us v', ∀ b z : v'.adicCompletion K, Φf v' (b * (t : v'.adicCompletion K), z) = Φf v' (b, z) :=
    fun v' hv' t ht b z => (hU v' hv').2 t (hUs_U v' ht) b z
  have hΦF0_inv : ∀ v : HeightOneSpectrum (𝓞 K), ∀ v' ∈ SK, ∀ t ∈ Us v', ∀ b z : v'.adicCompletion K,
      ΦF0 v v' (b * (t : v'.adicCompletion K), z) = ΦF0 v v' (b, z) := by
    intro v v' hv' t ht b z
    by_cases h : v' = v
    · subst h
      simp only [ΦF0, Function.update_self]
      exact (hU0 v' hv').2 t (hUs_U0 v' ht) b z
    · simp only [ΦF0, Function.update_of_ne h]
      exact hΦf_inv v' hv' t ht b z
  have hWf_inv : ∀ (ξ : ↥Ξ) (F : ∀ v' : HeightOneSpectrum (𝓞 K), (v'.adicCompletion K) × (v'.adicCompletion K) → ℂ),
      (∀ v' ∈ SK, ∀ t ∈ Us v', ∀ b z : v'.adicCompletion K, F v' (b * (t : v'.adicCompletion K), z) = F v' (b, z)) →
      ∀ g ∈ Hs, ∀ (u : Kˣ) (x : mixedEmbedding.mixedSpace K), Wf ξ F x (bS (u * g)) = Wf ξ F x (bS u) := by
    intro ξ F hF g hg u x
    simp only [Wf, hprodInv F hF g hg u]

  let ecx := Fintype.equivFin {w : NumberField.InfinitePlace K // w.IsComplex}
  let θ₀v : Kˣ → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) := fun u J =>
    if h : ∃ w : {w : NumberField.InfinitePlace K // w.IsComplex}, cw w = J then arg (emb u) (ecx h.choose) else 0
  have hθ₀v_cw : ∀ (u : Kˣ) (w : {w : NumberField.InfinitePlace K // w.IsComplex}), θ₀v u (cw w) = arg (emb u) (ecx w) := by
    intro u w
    have h : ∃ w' : {w : NumberField.InfinitePlace K // w.IsComplex}, cw w' = cw w := ⟨w, rfl⟩
    simp only [θ₀v, dif_pos h]
    rw [hcw h.choose_spec]
  have hθ₀v_cs : ∀ (u : Kˣ) (j : Fin (NumberField.InfinitePlace.nrComplexPlaces K)), θ₀v u (cs j) = arg (emb u) j := by
    intro u j
    rw [hcs_cw, hθ₀v_cw]
    simp only [ecx, Equiv.apply_symm_apply]
  have hθ₀v_ts : ∀ (u : Kˣ) (j : Fin T.card), θ₀v u (ts j) = 0 := by
    intro u j
    have h : ¬ ∃ w : {w : NumberField.InfinitePlace K // w.IsComplex}, cw w = ts j := by
      rintro ⟨w, hw⟩
      have h1 := Fin.castAdd_lt T.card (ιw w.1)
      have h2 : ((ts j : Fin _) : ℕ) = Fintype.card (NumberField.InfinitePlace K) + (j : ℕ) := Fin.val_natAdd _ _
      have h3 : ((cw w : Fin _) : ℕ) = ((ts j : Fin _) : ℕ) := by rw [hw]
      simp only [cw] at h1 h3
      omega
    simp only [θ₀v, dif_neg h]

  have hexp_congr : ∀ (a : ℂ) (s t : ℝ), ((s : ℝ) : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ)) →
      Complex.exp (a + 2 * Real.pi * Complex.I * ((s : ℝ) : ℂ)) = Complex.exp (a + 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := by
    intro a s t h
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨k, hk⟩ := h
    have hs : s = t + k := by rw [zsmul_eq_mul, mul_one] at hk; linarith
    rw [hs, show a + 2 * Real.pi * Complex.I * ((t + k : ℝ) : ℂ) = (a + 2 * Real.pi * Complex.I * (t : ℂ)) + k * (2 * Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

  have halg : ∀ (s : Finset ↥Ξ) (SR SC : Finset (NumberField.InfinitePlace K)) (a : ↥Ξ → ℂ)
      (b c : NumberField.InfinitePlace K → ↥Ξ → ℂ) (κ μ' : NumberField.InfinitePlace K → ℂ) (t : ℂ),
      C * (t * (c' * ∑ ξ ∈ s, (a ξ + ∑ w ∈ SR, κ w * b w ξ + ∑ w ∈ SC, μ' w * c w ξ))) =
        t * (C * (c' * ∑ ξ ∈ s, a ξ) + ∑ w ∈ SR, κ w * (C * (c' * ∑ ξ ∈ s, b w ξ)) +
          ∑ w ∈ SC, μ' w * (C * (c' * ∑ ξ ∈ s, c w ξ))) := by
    intro s SR SC a b c κ μ' t
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

  have hcondG : ∀ (n : Fin T.card → ℤ) (u : Kˣ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero u = 1) →
      (∀ j : Fin T.card, (f (T.equivFin.symm j).1 : ℤ) ∣ (Log u).2 j) →
      ∀ g ∈ Hs, (u * g ∈ I' n ↔ (Lmap g).2 + n₀f u = n) := by
    intro n u huT hudvd g hg
    have hgA := hHsA hg
    rw [hI'_val]
    constructor
    · rintro ⟨-, h2⟩
      funext j
      have hj := h2 j
      rw [hLog_mul, Prod.snd_add, Pi.add_apply] at hj
      show -((Log g).2 j / (f (T.equivFin.symm j).1 : ℤ)) + -((Log u).2 j / (f (T.equivFin.symm j).1 : ℤ)) = n j
      apply mul_left_cancel₀ (hf0 j)
      rw [mul_add, mul_neg, mul_neg, Int.mul_ediv_cancel' (hfdvd g hgA j), Int.mul_ediv_cancel' (hudvd j)]
      linarith
    · intro hn
      refine ⟨fun v hvS hvT => by rw [map_mul, huT v hvS hvT, ((hA_mem g).1 hgA).1 v hvT, mul_one], fun j => ?_⟩
      have hj := congr_fun hn j
      simp only [Pi.add_apply] at hj
      rw [hLog_mul, Prod.snd_add, Pi.add_apply]
      have e1 := Int.mul_ediv_cancel' (hfdvd g hgA j)
      have e2 := Int.mul_ediv_cancel' (hudvd j)
      rw [← hj, mul_add, mul_neg, mul_neg, e1, e2]
      ring
  have hembG : ∀ (u : Kˣ), ∀ g ∈ Hs,
      emb (u * g) = P (sgn (emb u)) ((Log u).1, 0) * P 1 ((Log g).1, arg (emb u) + arg (emb g)) := by
    intro u g hg
    obtain ⟨-, -, -, hgpos⟩ := (hHs_mem g).1 hg
    have h1 : sgn (emb g) = 1 := hsgn1 (emb g) (hemb_unit g) (fun w => by rw [hemb]; exact hgpos w)
    rw [hemb_mul]
    conv_lhs => rw [← hP_inv' u, ← hP_inv' g, h1]
    rw [← hP_mul, ← hP_mul, zero_add]
  have hsgnG : ∀ (u : Kˣ), ∀ g ∈ Hs, sgn (emb (u * g)) = sgn (emb u) := by
    intro u g hg
    obtain ⟨-, -, -, hgpos⟩ := (hHs_mem g).1 hg
    have h1 : sgn (emb g) = 1 := hsgn1 (emb g) (hemb_unit g) (fun w => by rw [hemb]; exact hgpos w)
    rw [hemb_mul, (hP_sgnarg _ _ (hemb_unit u) (hemb_unit g)).1, h1, mul_one]
  have hargG : ∀ (u : Kˣ), ∀ g ∈ Hs, ∀ j,
      ((arg (emb (u * g)) j : ℝ) : AddCircle (1 : ℝ)) = (((arg (emb u) + arg (emb g)) j : ℝ) : AddCircle (1 : ℝ)) := by
    intro u g hg j
    obtain ⟨kv, hkv⟩ := (hP_sgnarg _ _ (hemb_unit u) (hemb_unit g)).2
    rw [hemb_mul, hkv]
    simp only [Pi.add_apply]
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
    exact ⟨kv j, by simp⟩
  have hkG : ∀ g ∈ Hs, ∀ j : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm j).1 (ιK g) =
      (f (T.equivFin.symm j).1 : ℤ) * (Lmap g).2 j := by
    intro g hg j
    rw [hord, ← hLog2]
    show -(Log g).2 j = (f (T.equivFin.symm j).1 : ℤ) * -((Log g).2 j / (f (T.equivFin.symm j).1 : ℤ))
    rw [mul_neg, Int.mul_ediv_cancel' (hfdvd g (hHsA hg) j)]
  have hℓG : ∀ g ∈ Hs, Real.exp (ℓ (Lmap g).1) = ∏ j, ‖tvec j‖ ^ (-((Lmap g).2 j)) := by
    intro g hg
    have := hℓ g (hF_T g (hHsF hg)) (fun j => (Lmap g).2 j) (hkG g hg)
    have hX : (fun i => (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
        Real.log (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) (g : K))) = (Lmap g).1 := by
      show _ = (Log g).1
      rw [hLog]
    rw [hX] at this
    exact this
  have hcsG : ∀ (u : Kˣ), ∀ g ∈ Hs, ∀ j,
      ((((θ₀v u + lift (Lmap g)) (cs j)) : ℝ) : AddCircle (1 : ℝ)) = (((arg (emb u) + arg (emb g)) j : ℝ) : AddCircle (1 : ℝ)) := by
    intro u g hg j
    simp only [Pi.add_apply]
    rw [hθ₀v_cs, hemb g]
    have := (hliftF g (hHsFA hg)).1 ((Fintype.equivFin {w : NumberField.InfinitePlace K // w.IsComplex}).symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [AddCircle.coe_add, AddCircle.coe_add, this]
  have htsG : ∀ (u : Kˣ), ∀ g ∈ Hs, ∀ j,
      ((((θ₀v u + lift (Lmap g)) (ts j)) : ℝ) : AddCircle (1 : ℝ)) =
        ((-((Lmap g).2 j : ℝ) * (tvec j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
    intro u g hg j
    simp only [Pi.add_apply]
    rw [hθ₀v_ts, zero_add, (hliftF g (hHsFA hg)).2 j]
    congr 1
    simp only [bvec]
    ring
  have htiltG : ∀ (n : Fin T.card → ℤ) (u : Kˣ) (g : Kˣ), (Lmap g).2 + n₀f u = n →
      tilt n = ∏ j, tvec j ^ (-(n₀f u j + (Lmap g).2 j)) := by
    intro n u g hc
    simp only [tilt]
    exact Finset.prod_congr rfl fun j _ => by rw [← hc]; simp only [Pi.add_apply]; ring_nf

  let KRs : Kˣ → InfinitePlace K → ℝ := fun u w =>
    ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖
  let gA : (Fin T.card → ℤ) → Kˣ → ℂ := fun n u => tilt n * (c' * ∑ ξ : ↥Ξ,
      ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (ARCH u zS * ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))))
  let g0 : (Fin T.card → ℤ) → ↥SK → Kˣ → ℂ := fun n v u =>
    tilt n * (c' * ∑ ξ : ↥Ξ, ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ) * Wf ξ (ΦF0 v.1) (emb u) (bS u))
  let KA : I₀ → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ := fun i p =>
    BwA i p + ∑ k' : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}), ((|1 - Real.exp (p.1 (kR k'))| : ℝ) : ℂ) * CwA i k' p +
      ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card),
        ((‖(1 : ℂ) - Complex.exp ((((p.1 (kC j)) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((p.2 j : ℝ) : ℂ))‖ ^ 2 *
          Real.log ‖(1 : ℂ) - Complex.exp ((((p.1 (kC j)) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((p.2 j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
        EwA i j p
  have hidA : ∀ (n : Fin T.card → ℤ) (i : I₀), ∀ g ∈ Hs, ((urep i * g : Kˣ) : K) ≠ 1 →
      C * (if urep i * g ∈ I' n then gA n (urep i * g) else 0) =
        1 * (if (Lmap g).2 + n₀f (urep i) = n then
          KA i ((Log (urep i)).1 + (Lmap g).1, θ₀v (urep i) + lift (Lmap g)) else 0) := by
    intro n i g hg hne
    rw [one_mul]
    rcases em ((Lmap g).2 + n₀f (urep i) = n) with hc | hc
    · rw [if_pos ((hcondG n (urep i) (hurep_T i) (hurep_dvd i) g hg).2 hc), if_pos hc]

      have hint : ∀ ξ : ↥Ξ, (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (ARCH (urep i * g) zS * ∏ v ∈ SK, Φf v (bS (urep i * g) v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
          Bt ξ (emb (urep i * g)) (bS (urep i)) +
            ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((KRs (urep i * g) w : ℝ) : ℂ) * Ct ξ w (emb (urep i * g)) (bS (urep i)) +
            ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
              ((KRs (urep i * g) w ^ 2 * Real.log (KRs (urep i * g) w) : ℝ) : ℂ) * Et ξ w (emb (urep i * g)) (bS (urep i)) := by
        intro ξ
        rw [show (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (ARCH (urep i * g) zS * ∏ v ∈ SK, Φf v (bS (urep i * g) v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))) =
            fun zS => ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
              (ARCH (urep i * g) zS * ∏ v ∈ SK, Φf v (bS (urep i) v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) from
            funext fun zS => by rw [hprodInv Φf hΦf_inv g hg (urep i)]]
        exact (hBCE_id ξ (urep i * g) hne (bS (urep i))).2
      have hL : C * gA n (urep i * g) = tilt n * (WB i (emb (urep i * g)) +
          ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((KRs (urep i * g) w : ℝ) : ℂ) * WC i w (emb (urep i * g)) +
          ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
            ((KRs (urep i * g) w ^ 2 * Real.log (KRs (urep i * g) w) : ℝ) : ℂ) * WE i w (emb (urep i * g))) := by
        simp only [gA, hint, WB, WC, WE]
        exact halg Finset.univ _ _ (fun ξ => Bt ξ (emb (urep i * g)) (bS (urep i)))
          (fun w ξ => Ct ξ w (emb (urep i * g)) (bS (urep i))) (fun w ξ => Et ξ w (emb (urep i * g)) (bS (urep i))) _ _ (tilt n)
      rw [hL]
      have hid := hA_id i (Lmap g).1 (arg (emb (urep i)) + arg (emb g)) (fun j => (Lmap g).2 j) (θ₀v (urep i) + lift (Lmap g))
        (hcsG _ g hg) (htsG _ g hg) (hℓG g hg)
      simp only [KA]
      rw [hid, ← htiltG n (urep i) g hc, hLmap1, ← hembG (urep i) g hg]
      congr 1
      have hX : (Log (urep i)).1 + (Log g).1 = (Log (urep i * g)).1 := by rw [hLog_mul (urep i) g]; rfl
      congr 1
      · congr 1
        refine Finset.sum_congr rfl fun w hw => ?_
        have hw' : w.IsReal := (Finset.mem_filter.1 hw).2
        rw [dif_pos hw', hX]
        congr 1
        simp only [KRs]
        rw [hKR (urep i * g) w hw', hsgnG _ g hg]
      · refine Finset.sum_congr rfl fun w hw => ?_
        have hw' : w.IsComplex := (Finset.mem_filter.1 hw).2
        rw [dif_pos hw', hX]
        congr 1
        have hΘ : (((θ₀v (urep i) + lift (Lmap g)) (cw ⟨w, hw'⟩) : ℝ) : AddCircle (1 : ℝ)) =
            (((arg (emb (urep i * g)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw'⟩)) : ℝ) : AddCircle (1 : ℝ)) := by
          have h1 := hcsG (urep i) g hg (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, hw'⟩)
          rw [hcs_cw] at h1
          simp only [Equiv.symm_apply_apply] at h1
          rw [h1, hargG _ g hg]
        have hζ := hexp_congr ((((Log (urep i * g)).1 (ιw w) / 2 : ℝ) : ℂ)) _ _ hΘ
        simp only [KRs]
        rw [(hKC (urep i * g) w hw').2, hζ]
    · rw [if_neg (mt (hcondG n (urep i) (hurep_T i) (hurep_dvd i) g hg).1 hc), if_neg hc, mul_zero]

  have hid0 : ∀ (n : Fin T.card → ℤ) (i : I₀) (v : ↥SK), ∀ g ∈ Hs, ((urep i * g : Kˣ) : K) ≠ 1 →
      C * (if urep i * g ∈ I' n then g0 n v (urep i * g) else 0) =
        ((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ) * (if (Lmap g).2 + n₀f (urep i) = n then
          G0 i v ((Log (urep i)).1 + (Lmap g).1, θ₀v (urep i) + lift (Lmap g)) else 0) := by
    intro n i v g hg hne
    rcases em ((Lmap g).2 + n₀f (urep i) = n) with hc | hc
    · rw [if_pos ((hcondG n (urep i) (hurep_T i) (hurep_dvd i) g hg).2 hc), if_pos hc]
      have hid := hG0_id i v (Lmap g).1 (arg (emb (urep i)) + arg (emb g)) (fun j => (Lmap g).2 j) (θ₀v (urep i) + lift (Lmap g))
        (hcsG _ g hg) (htsG _ g hg) (hℓG g hg)
      rw [hid, ← htiltG n (urep i) g hc, hLmap1, ← hembG (urep i) g hg]
      simp only [g0, W0, hsqrtA (urep i) g hg v.1 v.2, hWf_inv _ (ΦF0 v.1) (hΦF0_inv v.1) g hg (urep i)]
      rw [← Finset.mul_sum]
      ring
    · rw [if_neg (mt (hcondG n (urep i) (hurep_T i) (hurep_dvd i) g hg).1 hc), if_neg hc, mul_zero, mul_zero]

  have hHvk_ex : ∀ (v : ↥SK) (k : ℕ), ∃ Hk : Subgroup Kˣ, ∀ g, g ∈ Hk ↔ g ∈ Hs ∧ uv g v.1 ∈ Vv v.1 k := by
    intro v k
    refine ⟨{ carrier := {g | g ∈ Hs ∧ uv g v.1 ∈ Vv v.1 k}
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨Hs.mul_mem ha hb, ?_⟩
      rw [huv_mul]
      exact (Vv v.1 k).mul_mem ha' hb'
    · refine ⟨Hs.one_mem, ?_⟩
      simp only [uv, map_one]
      exact (Vv v.1 k).one_mem
    · rintro a ⟨ha, ha'⟩
      refine ⟨Hs.inv_mem ha, ?_⟩
      simp only [uv, map_inv]
      exact (Vv v.1 k).inv_mem ha'
  choose Hvk hHvk_mem using hHvk_ex
  have hHvk_Hs : ∀ v k, Hvk v k ≤ Hs := fun v k g hg => ((hHvk_mem v k g).1 hg).1
  have hHvk_FA : ∀ v k, Hvk v k ≤ FA := fun v k => (hHvk_Hs v k).trans hHsFA
  let gc : (Fin T.card → ℤ) → (v : ↥SK) → ℕ → (v.1.adicCompletion K)ˣ → (v.1.adicCompletion K)ˣ → Kˣ → ℂ :=
    fun n v k α τ u => if (uv u v.1)⁻¹ ∈ sh v.1 k then
      tilt n * (c' * ∑ ξ : ↥Ξ, ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ) * (cv v.1 k α τ * Wf ξ (ΦFc v.1 k α τ) (emb u) (bS u))) else 0

  have hδ_ex : ∀ (i : I₀) (v : ↥SK) (k : ℕ) (τ : (v.1.adicCompletion K)ˣ), ∃ δ : Kˣ,
      (∃ g ∈ Hs, uv (urep i * g) v.1 * τ ∈ Vv v.1 k) → (δ ∈ Hs ∧ uv (urep i * δ) v.1 * τ ∈ Vv v.1 k) := by
    intro i v k τ
    by_cases h : ∃ g ∈ Hs, uv (urep i * g) v.1 * τ ∈ Vv v.1 k
    · obtain ⟨g, hg, hg'⟩ := h
      exact ⟨g, fun _ => ⟨hg, hg'⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose δf hδf using hδ_ex

  have hshell_iff : ∀ (v : ↥SK) (k : ℕ) (t τ : (v.1.adicCompletion K)ˣ), t * τ ∈ Vv v.1 k →
      (t⁻¹ ∈ sh v.1 k ↔ τ ∈ sh v.1 k) := by
    intro v k t τ ht
    have hshV := (hDSv v.1 v.2).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    constructor
    · intro h
      have := hshV k _ h _ ht
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · intro h
      have := hshV k _ h _ ((Vv v.1 k).inv_mem ht)
      rwa [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at this

  have hΦc_eq_Φd : ∀ (v : ↥SK) (k : ℕ) (α τ b₀ σ : (v.1.adicCompletion K)ˣ), σ ∈ Av v.1 → b₀ * σ * τ ∈ Vv v.1 k →
      ∀ z : v.1.adicCompletion K, Φc v.1 k α τ (((b₀ * σ : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K), z) =
        Φd v.1 α b₀ ((b₀ : v.1.adicCompletion K), z) := by
    intro v k α τ b₀ σ hσ hV z
    rcases em (z = 0) with hz | hz
    · subst hz
      have h1 : Φc v.1 k α τ (((b₀ * σ : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K), 0) = 0 := by
        by_contra h; exact ((hΦc v.1 k α τ v.2).2.2.1 _ h).2 rfl
      have h2 : Φd v.1 α b₀ ((b₀ : v.1.adicCompletion K), 0) = 0 := by
        by_contra h; exact ((hΦd v.1 α b₀ v.2).2.2.1 _ h).2 rfl
      rw [h1, h2]
    · have hzu : z = ((Units.mk0 z hz : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) := rfl
      rw [hzu, (hΦc v.1 k α τ v.2).2.2.2.1, (hΦd v.1 α b₀ v.2).2.2.2]
      have hA : ((Units.mk0 z hz) * (b₀ * σ))⁻¹ * α ∈ Av v.1 ↔ ((Units.mk0 z hz) * b₀)⁻¹ * α ∈ Av v.1 := by
        have : ((Units.mk0 z hz) * (b₀ * σ))⁻¹ * α = σ⁻¹ * (((Units.mk0 z hz) * b₀)⁻¹ * α) := by
          simp only [mul_inv_rev, mul_assoc]
        rw [this]
        constructor
        · intro h
          have := (Av v.1).mul_mem hσ h
          rwa [← mul_assoc, mul_inv_cancel, one_mul] at this
        · intro h
          exact (Av v.1).mul_mem ((Av v.1).inv_mem hσ) h
      have hB : b₀ * b₀⁻¹ ∈ Av v.1 := by rw [mul_inv_cancel]; exact (Av v.1).one_mem
      by_cases h : ((Units.mk0 z hz) * b₀)⁻¹ * α ∈ Av v.1
      · rw [if_pos ⟨hA.2 h, hV⟩, if_pos ⟨h, hB⟩]
      · rw [if_neg (fun h' => h (hA.1 h'.1)), if_neg (fun h' => h h'.1)]
  have hWc_frozen : ∀ (i : I₀) (v : ↥SK) (k : ℕ) (α : ↥(Fa v.1)) (τ : (v.1.adicCompletion K)ˣ), ∀ g ∈ Hs,
      uv (urep i * g) v.1 * τ ∈ Vv v.1 k → ∀ (ξ : ↥Ξ) (x : mixedEmbedding.mixedSpace K),
      Wf ξ (ΦFc v.1 k α.1 τ) x (bS (urep i * g)) = Wf ξ (ΦFd v.1 α.1 (uv (urep i) v.1)) x (bS (urep i)) := by
    intro i v k α τ g hg hV ξ x
    simp only [Wf]
    congr 1
    funext zS
    congr 2
    refine Finset.prod_congr rfl fun v' hv' => ?_
    by_cases h : v' = v.1
    · subst h
      simp only [ΦFc, ΦFd, Function.update_self]
      rw [← huv, ← huv, huv_mul]
      rw [huv_mul] at hV
      exact hΦc_eq_Φd v k α.1 τ (uv (urep i) v.1) (uv g v.1) (hUs_A _ (huv_Us g hg _ v.2)) hV _
    · simp only [ΦFc, ΦFd, Function.update_of_ne h]
      rw [hbS_mul, ← huv g v']
      exact hΦf_inv v' hv' _ (huv_Us g hg v' hv') _ _

  have hlift_add : ∀ a ∈ FA, ∀ b ∈ FA, ∃ m : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℤ,
      lift (Lmap a) + lift (Lmap b) = lift (Lmap (a * b)) + fun J => (m J : ℝ) := by
    intro a ha b hb
    have haΛ : Lmap a ∈ Λ := (hΛ' _).2 ⟨a, ha, rfl⟩
    have hbΛ : Lmap b ∈ Λ := (hΛ' _).2 ⟨b, hb, rfl⟩
    have habΛ : Lmap (a * b) ∈ Λ := (hΛ' _).2 ⟨a * b, FA.mul_mem ha hb, rfl⟩
    have hJ : ∀ J, ∃ m : ℤ, lift (Lmap a) J + lift (Lmap b) J = lift (Lmap (a * b)) J + m := by
      intro J
      have h1 := hcompat _ haΛ J
      have h2 := hcompat _ hbΛ J
      have h3 := hcompat _ habΛ J
      have hsum : (⟨Lmap (a * b), habΛ⟩ : Λ) = ⟨Lmap a, haΛ⟩ + ⟨Lmap b, hbΛ⟩ := by
        apply Subtype.ext
        show Lmap (a * b) = Lmap a + Lmap b
        exact hL_add a ha b hb
      have : (((lift (Lmap a) J + lift (Lmap b) J) : ℝ) : AddCircle (1 : ℝ)) = ((lift (Lmap (a * b)) J : ℝ) : AddCircle (1 : ℝ)) := by
        rw [AddCircle.coe_add, h1, h2, h3, hsum, map_add]
        rfl
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, by rw [zsmul_eq_mul, mul_one] at hm; linarith⟩
    choose m hm using hJ
    exact ⟨m, funext fun J => by simp only [Pi.add_apply]; exact hm J⟩
  have hidc : ∀ (n : Fin T.card → ℤ) (i : I₀) (v : ↥SK) (k : ℕ) (α : ↥(Fa v.1)) (τ : (v.1.adicCompletion K)ˣ),
      (∃ g ∈ Hs, uv (urep i * g) v.1 * τ ∈ Vv v.1 k) →
      ∀ g' ∈ Hvk v k, ((urep i * δf i v k τ * g' : Kˣ) : K) ≠ 1 →
      C * (if urep i * δf i v k τ * g' ∈ I' n then gc n v k α.1 τ (urep i * δf i v k τ * g') else 0) =
        ((if τ ∈ sh v.1 k then 1 else 0) * ((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ) * cv v.1 k α.1 τ) *
          (if (Lmap g').2 + (n₀f (urep i) + (Lmap (δf i v k τ)).2) = n then
            Gc i ⟨v, α⟩ (((Log (urep i)).1 + (Lmap (δf i v k τ)).1) + (Lmap g').1,
              (θ₀v (urep i) + lift (Lmap (δf i v k τ))) + lift (Lmap g')) else 0) := by
    intro n i v k α τ hfire g' hg' hne
    obtain ⟨hδ, hδV⟩ := hδf i v k τ hfire
    obtain ⟨hg's, hg'V⟩ := (hHvk_mem v k g').1 hg'
    have hG : δf i v k τ * g' ∈ Hs := Hs.mul_mem hδ hg's
    have hassoc : urep i * δf i v k τ * g' = urep i * (δf i v k τ * g') := mul_assoc _ _ _
    have hV : uv (urep i * (δf i v k τ * g')) v.1 * τ ∈ Vv v.1 k := by
      rw [← mul_assoc, huv_mul (urep i * δf i v k τ) g', mul_right_comm]
      exact (Vv v.1 k).mul_mem hδV hg'V
    have hL2 : (Lmap (δf i v k τ * g')).2 = (Lmap (δf i v k τ)).2 + (Lmap g').2 := by
      rw [hL_add _ (hHsFA hδ) _ (hHsFA hg's)]; rfl
    have hL1 : (Lmap (δf i v k τ * g')).1 = (Lmap (δf i v k τ)).1 + (Lmap g').1 := by
      rw [hL_add _ (hHsFA hδ) _ (hHsFA hg's)]; rfl
    have hfib : ((Lmap g').2 + (n₀f (urep i) + (Lmap (δf i v k τ)).2) = n) ↔ ((Lmap (δf i v k τ * g')).2 + n₀f (urep i) = n) := by
      rw [hL2]
      constructor <;> intro h <;> rw [← h] <;> abel
    rw [hassoc]
    rcases em ((Lmap (δf i v k τ * g')).2 + n₀f (urep i) = n) with hc | hc
    · rw [if_pos ((hcondG n (urep i) (hurep_T i) (hurep_dvd i) _ hG).2 hc), if_pos (hfib.2 hc)]
      have hsh : ((uv (urep i * (δf i v k τ * g')) v.1)⁻¹ ∈ sh v.1 k) ↔ τ ∈ sh v.1 k := hshell_iff v k _ τ hV
      by_cases hτ : τ ∈ sh v.1 k
      ·
        obtain ⟨m, hm⟩ := hlift_add _ (hHsFA hδ) _ (hHsFA hg's)
        have hΘ : (θ₀v (urep i) + lift (Lmap (δf i v k τ))) + lift (Lmap g') =
            (θ₀v (urep i) + lift (Lmap (δf i v k τ * g'))) + fun J => (m J : ℝ) := by
          rw [add_assoc, hm, ← add_assoc]
        have hid := hGc_id i ⟨v, α⟩ (Lmap (δf i v k τ * g')).1 (arg (emb (urep i)) + arg (emb (δf i v k τ * g')))
          (fun j => (Lmap (δf i v k τ * g')).2 j) (θ₀v (urep i) + lift (Lmap (δf i v k τ * g')))
          (hcsG _ _ hG) (htsG _ _ hG) (hℓG _ hG)
        rw [hΘ, hper_int (Gc i ⟨v, α⟩) (hGc_per i ⟨v, α⟩), add_assoc ((Log (urep i)).1), ← hL1, hid, ← htiltG n (urep i) _ hc, hLmap1,
          ← hembG (urep i) _ hG, if_pos hτ]
        simp only [gc, if_pos (hsh.2 hτ), Wc, hsqrtA (urep i) _ hG v.1 v.2,
          hWc_frozen i v k α τ _ hG hV]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        ring
      · rw [if_neg hτ]
        simp only [gc, if_neg (fun h => hτ (hsh.1 h)), mul_zero, zero_mul]
    · rw [if_neg (mt (hcondG n (urep i) (hurep_T i) (hurep_dvd i) _ hG).1 hc), if_neg (fun h => hc (hfib.1 h)), mul_zero, mul_zero]

  let Sh := I₀ × (Unit ⊕ ↥SK ⊕ Shc)
  let A₀ : ℕ := Fintype.card Sh
  let eSh : Sh ≃ Fin A₀ := Fintype.equivFin Sh
  let BwS : Sh → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ := fun s => Sum.elim (fun _ => BwA s.1) (Sum.elim (fun v => G0 s.1 v) (fun p => Gc s.1 p)) s.2
  let CwS : Sh → Fin (Fintype.card {w : InfinitePlace K // w.IsReal}) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ :=
    fun s => Sum.elim (fun _ => CwA s.1) (fun _ => 0) s.2
  let EwS : Sh → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ :=
    fun s => Sum.elim (fun _ => EwA s.1) (fun _ => 0) s.2

  let KS : Sh → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ := fun s p =>
    BwS s p + ∑ k' : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}), ((|1 - Real.exp (p.1 (kR k'))| : ℝ) : ℂ) * CwS s k' p +
      ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card),
        ((‖(1 : ℂ) - Complex.exp ((((p.1 (kC j)) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((p.2 j : ℝ) : ℂ))‖ ^ 2 *
          Real.log ‖(1 : ℂ) - Complex.exp ((((p.1 (kC j)) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((p.2 j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
        EwS s j p
  have hKS_A : ∀ (i : I₀) p, KS (i, Sum.inl ()) p = KA i p := fun i p => rfl
  have hKS_0 : ∀ (i : I₀) (v : ↥SK) p, KS (i, Sum.inr (Sum.inl v)) p = G0 i v p := by
    intro i v p; simp [KS, BwS, CwS, EwS]
  have hKS_c : ∀ (i : I₀) (q : Shc) p, KS (i, Sum.inr (Sum.inr q)) p = Gc i q p := by
    intro i q p; simp [KS, BwS, CwS, EwS]
  have hBwS_sm : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (BwS s) := by
    rintro ⟨i, (_ | v | q)⟩
    · exact (hA_sm i).1
    · exact hG0_sm i v
    · exact hGc_sm i q
  have hCwS_sm : ∀ s k', ContDiff ℝ (⊤ : ℕ∞) (CwS s k') := by
    rintro ⟨i, (_ | v | q)⟩ k'
    · exact (hA_sm i).2.1 k'
    · exact contDiff_const
    · exact contDiff_const
  have hEwS_sm : ∀ s j, ContDiff ℝ (⊤ : ℕ∞) (EwS s j) := by
    rintro ⟨i, (_ | v | q)⟩ j
    · exact (hA_sm i).2.2 j
    · exact contDiff_const
    · exact contDiff_const
  have hS_per : ∀ s (p : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))) (J : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
      BwS s (p.1, p.2 + Pi.single J 1) = BwS s p ∧ (∀ k', CwS s k' (p.1, p.2 + Pi.single J 1) = CwS s k' p) ∧
        ∀ j, EwS s j (p.1, p.2 + Pi.single J 1) = EwS s j p := by
    rintro ⟨i, (_ | v | q)⟩ p J
    · exact hA_per i p J
    · exact ⟨hG0_per i v p J, fun _ => rfl, fun _ => rfl⟩
    · exact ⟨hGc_per i q p J, fun _ => rfl, fun _ => rfl⟩

  let Rmax : ℝ := ∑ i : I₀, RbA i + ∑ i : I₀, ∑ v : ↥SK, Rb0 i v + ∑ i : I₀, ∑ q : Shc, Rbc i q
  have hRA_le : ∀ i, RbA i ≤ Rmax := fun i => by
    have h1 : RbA i ≤ ∑ i : I₀, RbA i := Finset.single_le_sum (fun i _ => hRbA i) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i : I₀, ∑ v : ↥SK, Rb0 i v := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v _ => hRb0 i v
    have h3 : 0 ≤ ∑ i : I₀, ∑ q : Shc, Rbc i q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun q _ => hRbc i q
    simp only [Rmax]; linarith
  have hR0_le : ∀ i v, Rb0 i v ≤ Rmax := fun i v => by
    have h1 : 0 ≤ ∑ i : I₀, RbA i := Finset.sum_nonneg fun i _ => hRbA i
    have h2 : Rb0 i v ≤ ∑ i : I₀, ∑ v : ↥SK, Rb0 i v :=
      (Finset.single_le_sum (fun v _ => hRb0 i v) (Finset.mem_univ v)).trans
        (Finset.single_le_sum (f := fun i => ∑ v : ↥SK, Rb0 i v) (fun i _ => Finset.sum_nonneg fun v _ => hRb0 i v) (Finset.mem_univ i))
    have h3 : 0 ≤ ∑ i : I₀, ∑ q : Shc, Rbc i q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun q _ => hRbc i q
    simp only [Rmax]; linarith
  have hRc_le : ∀ i q, Rbc i q ≤ Rmax := fun i q => by
    have h1 : 0 ≤ ∑ i : I₀, RbA i := Finset.sum_nonneg fun i _ => hRbA i
    have h2 : 0 ≤ ∑ i : I₀, ∑ v : ↥SK, Rb0 i v := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v _ => hRb0 i v
    have h3 : Rbc i q ≤ ∑ i : I₀, ∑ q : Shc, Rbc i q :=
      (Finset.single_le_sum (fun q _ => hRbc i q) (Finset.mem_univ q)).trans
        (Finset.single_le_sum (f := fun i => ∑ q : Shc, Rbc i q) (fun i _ => Finset.sum_nonneg fun q _ => hRbc i q) (Finset.mem_univ i))
    simp only [Rmax]; linarith
  let Sx : Set (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) := {x | ∀ i, |x i| ≤ Rmax}
  have hSx : IsCompact Sx := by
    have : Sx = Set.pi Set.univ (fun _ => Set.Icc (-Rmax) Rmax) := by
      ext x; simp only [Sx, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hS_supp : ∀ s (p : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))), p.1 ∉ Sx → BwS s p = 0 ∧ (∀ k', CwS s k' p = 0) ∧ ∀ j, EwS s j p = 0 := by
    intro s p hp
    simp only [Sx, Set.mem_setOf_eq, not_forall, not_le] at hp
    obtain ⟨i₀, hi₀⟩ := hp
    rcases s with ⟨i, (_ | v | q)⟩
    · exact hA_supp i p ⟨i₀, (hRA_le i).trans_lt hi₀⟩
    · exact ⟨hG0_supp i v p ⟨i₀, (hR0_le i v).trans_lt hi₀⟩, fun _ => rfl, fun _ => rfl⟩
    · exact ⟨hGc_supp i q p ⟨i₀, (hRc_le i q).trans_lt hi₀⟩, fun _ => rfl, fun _ => rfl⟩

  have hC'v : ∀ v ∈ SK, 0 ≤ C'v v := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbdv : ∀ v ∈ SK, ∀ k α τ, ‖cv v k α τ‖ ≤ C'v v * ((k : ℝ) + 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) :=
    fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcardv : ∀ v ∈ SK, ∀ k, (Ft v k).card ≤ M₀v v := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsepv : ∀ v ∈ SK, ∀ k, ∀ τ ∈ Ft v k, ∀ τ' ∈ Ft v k, τ ≠ τ' → τ⁻¹ * τ' ∉ Vv v k := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFav : ∀ v ∈ SK, ∀ α ∈ Fa v, ∀ α' ∈ Fa v, α ≠ α' → α⁻¹ * α' ∉ Av v := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsh1v : ∀ v ∈ SK, ∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh v k := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.1
  have hshdisjv : ∀ v ∈ SK, Pairwise fun k k' => Disjoint (sh v k) (sh v k') := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.1
  have hshVv : ∀ v ∈ SK, ∀ k, ∀ t ∈ sh v k, ∀ τ ∈ Vv v k, t * τ ∈ sh v k := fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hidv : ∀ v ∈ SK, ∀ k, ∀ a t : (v.adicCompletion K)ˣ, t ∈ sh v k →
      Ψf v (a, t) = Ψ₀ v (a, t) + ∑ α ∈ Fa v, ∑ τ ∈ Ft v k, cv v k α τ * (if a⁻¹ * α ∈ Av v ∧ t⁻¹ * τ ∈ Vv v k then 1 else 0) :=
    fun v hv => (hDSv v hv).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

  have hsh_V : ∀ v ∈ SK, ∀ k, ∀ τ ∈ sh v k, τ ∉ Vv v k := by
    intro v hv k τ hτ hV
    have := hshVv v hv k τ hτ τ⁻¹ ((Vv v k).inv_mem hV)
    rw [mul_inv_cancel] at this
    exact hsh1v v hv k this

  let TyC := ((I₀ × ↥SK) × ℕ) × (ℕ × ℕ)
  let TyR := (I₀ ⊕ (I₀ × ↥SK)) ⊕ TyC
  let Ty := TyR ⊕ TyR
  let αOf : (v : ↥SK) → ℕ → (v.1.adicCompletion K)ˣ := fun v a =>
    if h : a < (Fa v.1).card then (((Fa v.1).equivFin.symm ⟨a, h⟩ : ↥(Fa v.1)) : (v.1.adicCompletion K)ˣ) else 1
  let τOf : (v : ↥SK) → ℕ → ℕ → (v.1.adicCompletion K)ˣ := fun v k t =>
    if h : t < (Ft v.1 k).card then (((Ft v.1 k).equivFin.symm ⟨t, h⟩ : ↥(Ft v.1 k)) : (v.1.adicCompletion K)ˣ) else 1
  have hαOf_mem : ∀ (v : ↥SK) (a : ℕ) (h : a < (Fa v.1).card), αOf v a ∈ Fa v.1 := by
    intro v a h; simp only [αOf, dif_pos h]; exact ((Fa v.1).equivFin.symm ⟨a, h⟩).2
  have hτOf_mem : ∀ (v : ↥SK) (k t : ℕ) (h : t < (Ft v.1 k).card), τOf v k t ∈ Ft v.1 k := by
    intro v k t h; simp only [τOf, dif_pos h]; exact ((Ft v.1 k).equivFin.symm ⟨t, h⟩).2
  let fire : I₀ → (v : ↥SK) → ℕ → (v.1.adicCompletion K)ˣ → Prop := fun i v k τ =>
    ∃ g ∈ Hs, uv (urep i * g) v.1 * τ ∈ Vv v.1 k
  let H'T : TyR → Subgroup Kˣ := fun r => Sum.elim (fun _ => Hs) (fun c => Hvk c.1.1.2 c.1.2) r
  have hH'T : ∀ r, H'T r ≤ FA := by
    rintro (x | c)
    · exact hHsFA
    · exact hHvk_FA _ _
  let δT : TyC → Kˣ := fun c => δf c.1.1.1 c.1.1.2 c.1.2 (τOf c.1.1.2 c.1.2 c.2.2)
  let baseT : TyR → Kˣ := fun r => Sum.elim (Sum.elim urep (fun p => urep p.1)) (fun c => urep c.1.1.1 * δT c) r
  let lamC : I₀ → (v : ↥SK) → ℕ → ℕ → ℕ → ℂ := fun i v k a t =>
    if a < (Fa v.1).card ∧ t < (Ft v.1 k).card then
        @ite ℂ (fire i v k (τOf v k t)) (Classical.dec _)
          ((if τOf v k t ∈ sh v.1 k then 1 else 0) * ((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ) * cv v.1 k (αOf v a) (τOf v k t)) 0 else 0
  let lamR : TyR → ℂ := fun r => Sum.elim
      (Sum.elim (fun _ => (1 : ℂ)) (fun p => ((Real.sqrt ‖bS (urep p.1) p.2.1‖ : ℝ) : ℂ)))
      (fun c => lamC c.1.1.1 c.1.1.2 c.1.2 c.2.1 c.2.2) r
  let shapeC : I₀ → ↥SK → ℕ → Sh := fun i v a =>
    if h : a < (Fa v.1).card then (i, Sum.inr (Sum.inr ⟨v, (Fa v.1).equivFin.symm ⟨a, h⟩⟩)) else (i, Sum.inl ())
  let shapeR : TyR → Sh := fun r => Sum.elim (Sum.elim (fun i => (i, Sum.inl ())) (fun p => (p.1, Sum.inr (Sum.inl p.2))))
      (fun c => shapeC c.1.1.1 c.1.1.2 c.2.1) r
  let x₀R : TyR → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) := fun r => Sum.elim (Sum.elim (fun i => (Log (urep i)).1) (fun p => (Log (urep p.1)).1))
      (fun c => (Log (urep c.1.1.1)).1 + (Lmap (δT c)).1) r
  let θ₀R : TyR → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) := fun r => Sum.elim (Sum.elim (fun i => θ₀v (urep i)) (fun p => θ₀v (urep p.1)))
      (fun c => θ₀v (urep c.1.1.1) + lift (Lmap (δT c))) r
  let n₀R : TyR → (Fin T.card → ℤ) := fun r => Sum.elim (Sum.elim (fun i => n₀f (urep i)) (fun p => n₀f (urep p.1)))
      (fun c => n₀f (urep c.1.1.1) + (Lmap (δT c)).2) r
  let subT : Ty → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) := fun t => Sum.elim (fun r => SL (H'T r) (hH'T r)) (fun _ => ⊥) t
  let lamT : Ty → ℂ := fun t => Sum.elim lamR (fun r => -(lamR r * @ite ℂ ((baseT r)⁻¹ ∈ H'T r) (Classical.dec _) 1 0)) t
  let shapeT : Ty → Fin A₀ := fun t => eSh (shapeR (Sum.elim id id t))
  let x₀T : Ty → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) := fun t => Sum.elim x₀R (fun r => x₀R r + (Lmap (baseT r)⁻¹).1) t
  let θ₀T : Ty → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) := fun t => Sum.elim θ₀R (fun r => θ₀R r + lift (Lmap (baseT r)⁻¹)) t
  let n₀T : Ty → (Fin T.card → ℤ) := fun t => Sum.elim n₀R (fun r => n₀R r + (Lmap (baseT r)⁻¹).2) t
  have hsubT_le : ∀ t, subT t ≤ Λ := by
    rintro (r | r)
    · exact (hSL (H'T r) (hH'T r)).1
    · exact bot_le

  have hq2 : ∀ v : HeightOneSpectrum (𝓞 K), ∀ k : ℕ, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) ≤ (1 / 2 : ℝ) ^ k := by
    intro v k
    have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      exact_mod_cast this
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h2 k)
  let Mtot : ℝ := ∑ i : I₀, ∑ v : ↥SK, Real.sqrt ‖bS (urep i) v.1‖ * C'v v.1
  have hMtot : ∀ (i : I₀) (v : ↥SK), Real.sqrt ‖bS (urep i) v.1‖ * C'v v.1 ≤ Mtot := by
    intro i v
    have hnn : ∀ (i : I₀) (v : ↥SK), 0 ≤ Real.sqrt ‖bS (urep i) v.1‖ * C'v v.1 :=
      fun i v => mul_nonneg (Real.sqrt_nonneg _) (hC'v v.1 v.2)
    exact (Finset.single_le_sum (fun v _ => hnn i v) (Finset.mem_univ v)).trans
      (Finset.single_le_sum (f := fun i => ∑ v : ↥SK, Real.sqrt ‖bS (urep i) v.1‖ * C'v v.1)
        (fun i _ => Finset.sum_nonneg fun v _ => hnn i v) (Finset.mem_univ i))
  let Amax : ℕ := ∑ v : ↥SK, (Fa v.1).card
  let Mmax : ℕ := ∑ v : ↥SK, M₀v v.1
  have hAmax : ∀ v : ↥SK, (Fa v.1).card ≤ Amax := fun v =>
    Finset.single_le_sum (f := fun v : ↥SK => (Fa v.1).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hMmax : ∀ (v : ↥SK) k, (Ft v.1 k).card ≤ Mmax := fun v k =>
    (hcardv v.1 v.2 k).trans (Finset.single_le_sum (f := fun v : ↥SK => M₀v v.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
  let B1 : (I₀ × ↥SK) × ℕ → ℝ := fun p => Mtot * (((p.2 : ℕ) : ℝ) + 1) * (1 / 2 : ℝ) ^ p.2
  let bA : ℕ → ℝ := fun a => if a < Amax then 1 else 0
  let bT : ℕ → ℝ := fun t => if t < Mmax then 1 else 0
  let B2 : ℕ × ℕ → ℝ := fun q => bA q.1 * bT q.2
  let Bnd : TyC → ℝ := fun c => B1 c.1 * B2 c.2
  have hbA_nn : ∀ a, 0 ≤ bA a := fun a => by simp only [bA]; split_ifs <;> norm_num
  have hbT_nn : ∀ t, 0 ≤ bT t := fun t => by simp only [bT]; split_ifs <;> norm_num
  have hMtot_nn : 0 ≤ Mtot := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v _ =>
    mul_nonneg (Real.sqrt_nonneg _) (hC'v v.1 v.2)
  have hB1_nn : ∀ p, 0 ≤ B1 p := fun p => mul_nonneg (mul_nonneg hMtot_nn (by positivity)) (by positivity)
  have hB2_nn : ∀ q, 0 ≤ B2 q := fun q => mul_nonneg (hbA_nn _) (hbT_nn _)
  have hBnd_summ : Summable Bnd := by
    have hk : Summable (fun k : ℕ => Mtot * (((k : ℕ) : ℝ) + 1) * (1 / 2 : ℝ) ^ k) := by
      have ha : Summable (fun k : ℕ => ((k : ℝ) ^ 1 : ℝ) * (1 / 2 : ℝ) ^ k) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
      have hb : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
      refine ((ha.add hb).mul_left Mtot).congr fun k => ?_
      ring
    have hc : Summable (fun _ : I₀ × ↥SK => (1 : ℝ)) := Summable.of_finite
    have h1 : Summable B1 := by
      refine (hc.mul_of_nonneg hk (fun _ => zero_le_one) (fun k => ?_)).congr fun p => ?_
      · exact mul_nonneg (mul_nonneg hMtot_nn (by positivity)) (by positivity)
      · simp only [B1, one_mul]
    have ha' : Summable bA := by
      refine summable_of_ne_finset_zero (s := Finset.range Amax) fun a ha => ?_
      rw [Finset.mem_range] at ha
      simp only [bA, if_neg ha]
    have hb' : Summable bT := by
      refine summable_of_ne_finset_zero (s := Finset.range Mmax) fun a ha => ?_
      rw [Finset.mem_range] at ha
      simp only [bT, if_neg ha]
    have h2 : Summable B2 := ha'.mul_of_nonneg hb' hbA_nn hbT_nn
    exact h1.mul_of_nonneg h2 hB1_nn hB2_nn
  have hBnn : ∀ k : ℕ, 0 ≤ Mtot * (((k : ℕ) : ℝ) + 1) * (1 / 2 : ℝ) ^ k := fun k =>
    mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (Real.sqrt_nonneg _) (hC'v v.1 v.2)) (by positivity)) (by positivity)
  have hBnd_nn : ∀ c, 0 ≤ Bnd c := fun c => mul_nonneg (hB1_nn _) (hB2_nn _)
  have hlamR_bnd : ∀ c : TyC, ‖lamR (Sum.inr c)‖ ≤ Bnd c := by
    rintro ⟨⟨⟨i, v⟩, k⟩, ⟨a, t⟩⟩
    simp only [lamR, Sum.elim_inr, lamC]
    by_cases hval : a < (Fa v.1).card ∧ t < (Ft v.1 k).card
    · rw [if_pos hval]
      have hB : Bnd (((i, v), k), (a, t)) = Mtot * (((k : ℕ) : ℝ) + 1) * (1 / 2 : ℝ) ^ k := by
        simp only [Bnd, B1, B2, bA, bT, if_pos (lt_of_lt_of_le hval.1 (hAmax v)), if_pos (lt_of_lt_of_le hval.2 (hMmax v k)), mul_one]
      rw [hB]
      rcases Classical.dec (fire i v k (τOf v k t)) with hf | hf
      · rw [if_neg hf, norm_zero]; exact hBnn k
      · rw [if_pos hf]
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul (norm_mul_le _ _) (hbdv v.1 v.2 k _ _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans ?_
        have hs : ‖((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ)‖ = Real.sqrt ‖bS (urep i) v.1‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        have hι : ‖(if τOf v k t ∈ sh v.1 k then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
        rw [hs]
        have hA1 : ‖(if τOf v k t ∈ sh v.1 k then (1 : ℂ) else 0)‖ * Real.sqrt ‖bS (urep i) v.1‖ ≤ 1 * Real.sqrt ‖bS (urep i) v.1‖ :=
          mul_le_mul_of_nonneg_right hι (Real.sqrt_nonneg _)
        have hA2 : C'v v.1 * ((k : ℝ) + 1) * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-(k : ℤ)) ≤ C'v v.1 * ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (hq2 v.1 k) (mul_nonneg (hC'v v.1 v.2) (by positivity))
        have hA3 : 0 ≤ C'v v.1 * ((k : ℝ) + 1) * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-(k : ℤ)) :=
          mul_nonneg (mul_nonneg (hC'v v.1 v.2) (by positivity)) (zpow_nonneg (Nat.cast_nonneg _) _)
        calc ‖(if τOf v k t ∈ sh v.1 k then (1 : ℂ) else 0)‖ * Real.sqrt ‖bS (urep i) v.1‖ *
              (C'v v.1 * ((k : ℝ) + 1) * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-(k : ℤ)))
            ≤ 1 * Real.sqrt ‖bS (urep i) v.1‖ * (C'v v.1 * ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) :=
              mul_le_mul hA1 hA2 hA3 (by positivity)
          _ = (Real.sqrt ‖bS (urep i) v.1‖ * C'v v.1) * (((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) := by ring
          _ ≤ Mtot * (((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) := mul_le_mul_of_nonneg_right (hMtot i v) (by positivity)
          _ = Mtot * ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k := by ring
    · rw [if_neg hval, norm_zero]; exact hBnd_nn _
  have hlamR_summ : Summable (fun r : TyR => ‖lamR r‖) := by
    have hfin : Summable (fun x : I₀ ⊕ (I₀ × ↥SK) => ‖lamR (Sum.inl x)‖) := Summable.of_finite
    have hcel : Summable (fun c : TyC => ‖lamR (Sum.inr c)‖) :=
      Summable.of_nonneg_of_le (fun c => norm_nonneg _) hlamR_bnd hBnd_summ
    exact (HasSum.sum (f := fun r : TyR => ‖lamR r‖) hfin.hasSum hcel.hasSum).summable
  have hlamT_summ : Summable (fun t : Ty => ‖lamT t‖) := by
    have hg : Summable (fun r : TyR => ‖lamT (Sum.inr r)‖) := by
      refine Summable.of_nonneg_of_le (fun r => norm_nonneg _) (fun r => ?_) hlamR_summ
      show ‖-(lamR r * @ite ℂ ((baseT r)⁻¹ ∈ H'T r) (Classical.dec _) 1 0)‖ ≤ ‖lamR r‖
      rw [norm_neg, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rcases Classical.dec ((baseT r)⁻¹ ∈ H'T r) with h | h
      · rw [if_neg h, norm_zero]; exact zero_le_one
      · rw [if_pos h, norm_one]
    have hr : Summable (fun r : TyR => ‖lamT (Sum.inl r)‖) := hlamR_summ
    exact (HasSum.sum (f := fun t : Ty => ‖lamT t‖) hr.hasSum hg.hasSum).summable

  letI encI₀ : Encodable I₀ := Fintype.toEncodable I₀
  letI encSK : Encodable ↥SK := Fintype.toEncodable ↥SK
  let dec : ℕ → Option Ty := Encodable.decode₂ Ty
  have hdec_enc : ∀ t : Ty, dec (Encodable.encode t) = some t := fun t => Encodable.encodek₂ t
  have hdec_none : ∀ m, m ∉ Set.range (Encodable.encode : Ty → ℕ) → dec m = none := by
    intro m hm
    by_contra h
    exact hm (Encodable.decode₂_ne_none_iff.1 h)
  let BwF : Fin (A₀ + 1) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ := Fin.lastCases 0 (fun a => BwS (eSh.symm a))
  let CwF : Fin (A₀ + 1) → Fin (Fintype.card {w : InfinitePlace K // w.IsReal}) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ :=
    Fin.lastCases 0 (fun a => CwS (eSh.symm a))
  let EwF : Fin (A₀ + 1) → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ :=
    Fin.lastCases 0 (fun a => EwS (eSh.symm a))
  let subN : ℕ → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) := fun m => (dec m).elim ⊥ subT
  let shapeN : ℕ → Fin (A₀ + 1) := fun m => (dec m).elim (Fin.last A₀) (fun t => Fin.castSucc (shapeT t))
  let lamN : ℕ → ℂ := fun m => (dec m).elim 0 lamT
  let x₀N : ℕ → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) := fun m => (dec m).elim 0 x₀T
  let n₀N : ℕ → (Fin T.card → ℤ) := fun m => (dec m).elim 0 n₀T
  let θ₀N : ℕ → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) := fun m => (dec m).elim 0 θ₀T
  have hBwF_c : ∀ a, BwF (Fin.castSucc a) = BwS (eSh.symm a) := fun a => by simp only [BwF, Fin.lastCases_castSucc]
  have hCwF_c : ∀ a, CwF (Fin.castSucc a) = CwS (eSh.symm a) := fun a => by simp only [CwF, Fin.lastCases_castSucc]
  have hEwF_c : ∀ a, EwF (Fin.castSucc a) = EwS (eSh.symm a) := fun a => by simp only [EwF, Fin.lastCases_castSucc]
  have hBwF_l : BwF (Fin.last A₀) = 0 := by simp only [BwF, Fin.lastCases_last]
  have hCwF_l : CwF (Fin.last A₀) = 0 := by simp only [CwF, Fin.lastCases_last]
  have hEwF_l : EwF (Fin.last A₀) = 0 := by simp only [EwF, Fin.lastCases_last]

  let KF : (((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ) → (Fin (Fintype.card {w : InfinitePlace K // w.IsReal}) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ) →
      (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ) → ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ := fun B Cc E p =>
    B p + ∑ k' : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}), ((|1 - Real.exp (p.1 (kR k'))| : ℝ) : ℂ) * Cc k' p +
      ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card),
        ((‖(1 : ℂ) - Complex.exp ((((p.1 (kC j)) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((p.2 j : ℝ) : ℂ))‖ ^ 2 *
          Real.log ‖(1 : ℂ) - Complex.exp ((((p.1 (kC j)) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((p.2 j : ℝ) : ℂ))‖ : ℝ) : ℂ) * E j p
  have hKS_KF : ∀ s p, KS s p = KF (BwS s) (CwS s) (EwS s) p := fun s p => rfl

  have hboxC : ∀ u : Kˣ, emb u ∈ Call → ∀ i, |(Log u).1 i| ≤ R₀ := by
    intro u hu i
    have := hR₀ (sgn (emb u)) ((Log u).1) (arg (emb u)) (by rw [hP_inv' u]; exact hu)
    exact this i
  have hpat_urep : ∀ (i : I₀) (g : Kˣ), g ∈ A → pat (urep i * g) ∈ hBfinS.toFinset := by
    intro i g hg
    have hz : (i.2.1 : Kˣ) ∈ A := hμA ((hμfin.mem_toFinset).1 i.2.1.2)
    have : pat (urep i * g) = pat (ubS i.1) := by
      show pat (ubS i.1 * ((i.2.1 : Kˣ) * cCs i.2.2) * g) = pat (ubS i.1)
      rw [mul_assoc, hpat_mulA _ _ (A.mul_mem (A.mul_mem hz (hcAs i.2.2)) hg)]
    rw [this, hubpatS]
    exact i.1.2
  have hQs_of : ∀ (n : Fin T.card → ℤ), ∀ u ∈ I' n, (∀ v : ↥SK, bS u v.1 ∈ Cst v.1) → u ∈ Qs := by
    intro n u hu hC
    have hu' := (hI'_val n u).1 hu
    refine ⟨hu'.1, fun v hv => ?_, fun v => by rw [← hbS]; exact hC v⟩
    have := hu'.2 (T.equivFin ⟨v, hv⟩)
    rw [hLog2] at this
    simp only [Equiv.symm_apply_apply] at this
    rw [this]
    exact (dvd_mul_right _ _).neg_right

  have hsuppA : ∀ (n : Fin T.card → ℤ) (u : Kˣ), (u : K) ≠ 1 → gA n u ≠ 0 → emb u ∈ Call ∧ ∀ v : ↥SK, bS u v.1 ∈ Cst v.1 := by
    intro n u hu hne
    have h1 : (∑ ξ : ↥Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        (ARCH u zS * ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) ≠ 0 := by
      intro h0; apply hne; simp only [gA, h0, mul_zero]
    obtain ⟨ξ, -, hξ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    rw [(hBCE_id ξ u hu (bS u)).2] at hξ
    have hC : emb u ∈ C₁ ξ := by
      by_contra hc
      have hz := (hC₁ ξ).2.2 (emb u) (bS u) hc
      apply hξ
      simp only [emb] at hz
      rw [hz.1, Finset.sum_eq_zero (fun w _ => by rw [(hz.2 w).1, mul_zero]),
        Finset.sum_eq_zero (fun w _ => by rw [(hz.2 w).2, mul_zero]), add_zero, add_zero]
    have hCf : ∀ v : ↥SK, bS u v.1 ∈ CfA ξ v.1 := by
      intro v
      by_contra hc
      have hz := (hCfA ξ).2 (emb u) (bS u) ⟨v.1, v.2, hc⟩
      apply hξ
      simp only [emb] at hz
      rw [hz.1, Finset.sum_eq_zero (fun w _ => by rw [(hz.2 w).1, mul_zero]),
        Finset.sum_eq_zero (fun w _ => by rw [(hz.2 w).2, mul_zero]), add_zero, add_zero]
    exact ⟨Or.inr (Set.mem_iUnion.2 ⟨ξ, hC⟩), fun v => Or.inl (Or.inr (Set.mem_iUnion.2 ⟨ξ, hCf v⟩))⟩
  have hsupp0 : ∀ (n : Fin T.card → ℤ) (v : ↥SK) (u : Kˣ), g0 n v u ≠ 0 → emb u ∈ Call ∧ ∀ v' : ↥SK, bS u v'.1 ∈ Cst v'.1 := by
    intro n v u hne
    have h1 : (∑ ξ : ↥Ξ, ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ) * Wf ξ (ΦF0 v.1) (emb u) (bS u)) ≠ 0 := by
      intro h0; apply hne; simp only [g0, h0, mul_zero]
    obtain ⟨ξ, -, hξ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have hW : Wf ξ (ΦF0 v.1) (emb u) (bS u) ≠ 0 := fun h => hξ (by rw [h, mul_zero])
    refine ⟨Or.inl (hWf0 ξ _ _ _ hW), fun v' => ?_⟩
    obtain ⟨z, hz⟩ := hWf_supp ξ (ΦF0 v.1) (emb u) (bS u) hW v'.1 v'.2
    by_cases h : v'.1 = v.1
    · obtain ⟨v'', hv''⟩ := v'
      subst h
      have hz' : Φ0 v.1 (bS u v.1, z) ≠ 0 := by
        have : ΦF0 v.1 v.1 = Φ0 v.1 := by simp only [ΦF0, Function.update_self]
        rwa [this] at hz
      exact Or.inl (Or.inl (Or.inr (hfst_tsupp v.1 _ _ _ hz')))
    · have hz' : Φf v'.1 (bS u v'.1, z) ≠ 0 := by
        have : ΦF0 v.1 v'.1 = Φf v'.1 := by simp only [ΦF0, Function.update_of_ne h]
        rwa [this] at hz
      exact Or.inl (Or.inl (Or.inl (hfst_tsupp v'.1 _ _ _ hz')))
  have hsuppc : ∀ (n : Fin T.card → ℤ) (v : ↥SK) (k : ℕ), ∀ α ∈ Fa v.1, ∀ τ ∈ Ft v.1 k, ∀ (u : Kˣ), gc n v k α τ u ≠ 0 →
      (emb u ∈ Call ∧ ∀ v' : ↥SK, bS u v'.1 ∈ Cst v'.1) ∧ (uv u v.1)⁻¹ ∈ sh v.1 k ∧ uv u v.1 * τ ∈ Vv v.1 k := by
    intro n v k α hα τ hτ u hne
    have hsh : (uv u v.1)⁻¹ ∈ sh v.1 k := by
      by_contra h; apply hne; simp only [gc, if_neg h]
    have h1 : (∑ ξ : ↥Ξ, ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ) * (cv v.1 k α τ * Wf ξ (ΦFc v.1 k α τ) (emb u) (bS u))) ≠ 0 := by
      intro h0; apply hne; simp only [gc, if_pos hsh, h0, mul_zero]
    obtain ⟨ξ, -, hξ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have hc0 : cv v.1 k α τ ≠ 0 := fun h => hξ (by rw [h, zero_mul, mul_zero])
    have hW : Wf ξ (ΦFc v.1 k α τ) (emb u) (bS u) ≠ 0 := fun h => hξ (by rw [h, mul_zero, mul_zero])

    have hv_facts : bS u v.1 ∈ Cst v.1 ∧ uv u v.1 * τ ∈ Vv v.1 k := by
      obtain ⟨z, hz⟩ := hWf_supp ξ (ΦFc v.1 k α τ) (emb u) (bS u) hW v.1 v.2
      have hzc : Φc v.1 k α τ (bS u v.1, z) ≠ 0 := by
        have : ΦFc v.1 k α τ v.1 = Φc v.1 k α τ := by simp only [ΦFc, Function.update_self]
        rwa [this] at hz
      have hz0 : z ≠ 0 := ((hΦc v.1 k α τ v.2).2.2.1 _ hzc).2
      have hind : ((Units.mk0 z hz0) * uv u v.1)⁻¹ * α ∈ Av v.1 ∧ uv u v.1 * τ ∈ Vv v.1 k := by
        by_contra hn
        apply hzc
        rw [← huv u v.1, show z = ((Units.mk0 z hz0 : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) from rfl,
          (hΦc v.1 k α τ v.2).2.2.2.1, if_neg hn]
      have hcell := Subgroup.sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
        (Av v.1) (Vv v.1 k) (Fa v.1) (Ft v.1 k) (cv v.1 k) (hFav v.1 v.2) (hsepv v.1 v.2 k)
        ((Units.mk0 z hz0) * uv u v.1) (uv u v.1)⁻¹ α τ hα hτ hind.1 (by rw [inv_inv]; exact hind.2)
      have hΨ := hidv v.1 v.2 k ((Units.mk0 z hz0) * uv u v.1) (uv u v.1)⁻¹ hsh
      rw [hcell] at hΨ
      have hne' : Ψf v.1 ((Units.mk0 z hz0) * uv u v.1, (uv u v.1)⁻¹) ≠ 0 ∨ Ψ₀ v.1 ((Units.mk0 z hz0) * uv u v.1, (uv u v.1)⁻¹) ≠ 0 := by
        by_contra hb
        push_neg at hb
        rw [hb.1, hb.2, zero_add] at hΨ
        exact hc0 hΨ.symm
      have hmem : ((Units.mk0 z hz0) * uv u v.1, (uv u v.1)⁻¹) ∈ tsupport (Ψf v.1) ∪ tsupport (Ψ₀ v.1) := by
        rcases hne' with h' | h'
        · exact Or.inl (subset_tsupport _ (Function.mem_support.2 h'))
        · exact Or.inr (subset_tsupport _ (Function.mem_support.2 h'))
      have hD : uv u v.1 ∈ Dv v.1 := by
        show uv u v.1 ∈ (Prod.snd '' (tsupport (Ψf v.1) ∪ tsupport (Ψ₀ v.1)))⁻¹
        rw [Set.mem_inv]
        exact ⟨_, hmem, rfl⟩
      rw [← huv u v.1]
      exact ⟨Or.inr ⟨_, hD, rfl⟩, hind.2⟩
    refine ⟨⟨Or.inl (hWf0 ξ _ _ _ hW), fun v' => ?_⟩, hsh, hv_facts.2⟩
    by_cases h : v'.1 = v.1
    · have : bS u v'.1 ∈ Cst v'.1 := by
        obtain ⟨v'', hv''⟩ := v'
        subst h
        exact hv_facts.1
      exact this
    · obtain ⟨z, hz⟩ := hWf_supp ξ (ΦFc v.1 k α τ) (emb u) (bS u) hW v'.1 v'.2
      have hz' : Φf v'.1 (bS u v'.1, z) ≠ 0 := by
        have : ΦFc v.1 k α τ v'.1 = Φf v'.1 := by simp only [ΦFc, Function.update_of_ne h]
        rwa [this] at hz
      exact Or.inl (Or.inl (Or.inl (hfst_tsupp v'.1 _ _ _ hz')))

  have hmain : ∀ n : Fin T.card → ℤ, C * ∑ᶠ u ∈ In n, term n u =
      ∑' i : ℕ, lamN i * ∑' γ : subN i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀N i = n then
            BwF (shapeN i) (x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ k : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}), ((|1 - Real.exp ((x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kR k))| : ℝ) : ℂ) * CwF (shapeN i) k (x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card), ((‖(1 : ℂ) - Complex.exp ((((x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                    Real.log ‖(1 : ℂ) - Complex.exp ((((x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
                EwF (shapeN i) j (x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by
    intro n

    have hUfin : (I' n ∩ {u : Kˣ | (∀ i, |(Log u).1 i| ≤ R₀) ∧ pat u ∈ hBfinS.toFinset}).Finite := by
      refine (Set.Finite.biUnion (Set.finite_univ : (Set.univ : Set ↥hBfinS.toFinset).Finite) fun β _ =>
        ((hboxfin (R₀ + ∑ i, |(Log (ubS β)).1 i|) (fun j => -((f (T.equivFin.symm j).1 : ℤ) * n j) - (Log (ubS β)).2 j)).image
          fun a => ubS β * a)).subset ?_
      rintro u ⟨huI, hbox, hβ⟩
      have hu' := (hI'_val n u).1 huI
      have hb := hubQS ⟨pat u, hβ⟩
      have hpb : pat (ubS ⟨pat u, hβ⟩) = pat u := hubpatS ⟨pat u, hβ⟩
      refine Set.mem_biUnion (Set.mem_univ (⟨pat u, hβ⟩ : ↥hBfinS.toFinset)) ⟨(ubS ⟨pat u, hβ⟩)⁻¹ * u, ⟨?_, ?_, ?_⟩, by group⟩
      · intro v hvT
        rw [map_mul, map_inv]
        by_cases hvS : v ∈ SK
        · have := congr_fun hpb ⟨v, hvS⟩
          rw [hpat, hpat] at this
          rw [WithZero.coe_inj.1 this, inv_mul_cancel]
        · rw [hb.1 v hvS hvT, hu'.1 v hvS hvT, inv_one, one_mul]
      · intro i
        rw [hLog_mul, hLog_inv, Prod.fst_add, Prod.fst_neg, Pi.add_apply, Pi.neg_apply]
        have h1 := hbox i
        have h2 : |(Log (ubS ⟨pat u, hβ⟩)).1 i| ≤ ∑ i, |(Log (ubS ⟨pat u, hβ⟩)).1 i| :=
          Finset.single_le_sum (f := fun i => |(Log (ubS ⟨pat u, hβ⟩)).1 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
        calc |-(Log (ubS ⟨pat u, hβ⟩)).1 i + (Log u).1 i|
            ≤ |-(Log (ubS ⟨pat u, hβ⟩)).1 i| + |(Log u).1 i| := abs_add_le _ _
          _ ≤ _ := by rw [abs_neg]; linarith
      · funext j
        rw [hLog_mul, hLog_inv, Prod.snd_add, Prod.snd_neg, Pi.add_apply, Pi.neg_apply, hu'.2 j]
        ring
    let Uf : Finset Kˣ := hUfin.toFinset
    have hUf_mem : ∀ u, u ∈ I' n → (∀ i, |(Log u).1 i| ≤ R₀) → pat u ∈ hBfinS.toFinset → u ∈ Uf :=
      fun u h1 h2 h3 => hUfin.mem_toFinset.2 ⟨h1, h2, h3⟩
    have hUf_I : ∀ u ∈ Uf, u ∈ I' n := fun u hu => (hUfin.mem_toFinset.1 hu).1
    let Kall : Finset ℕ := Uf.biUnion (fun u => (Finset.univ : Finset ↥SK).biUnion (fun v =>
        if h : ∃ k, (uv u v.1)⁻¹ ∈ sh v.1 k then {h.choose} else ∅))
    have hKall : ∀ u ∈ Uf, ∀ (v : ↥SK) (k : ℕ), (uv u v.1)⁻¹ ∈ sh v.1 k → k ∈ Kall := by
      intro u hu v k hk
      refine Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, ?_⟩⟩
      have h : ∃ k, (uv u v.1)⁻¹ ∈ sh v.1 k := ⟨k, hk⟩
      rw [dif_pos h]
      have : h.choose = k := by
        by_contra hne
        exact Set.disjoint_left.1 (hshdisjv v.1 v.2 hne) h.choose_spec hk
      rw [this]; exact Finset.mem_singleton_self k

    have hshell_unique : ∀ (v : ↥SK) (t : (v.1.adicCompletion K)ˣ) (k k' : ℕ), t ∈ sh v.1 k → t ∈ sh v.1 k' → k = k' := by
      intro v t k k' h h'
      by_contra hne
      exact Set.disjoint_left.1 (hshdisjv v.1 v.2 hne) h h'

    have hQs_piece : ∀ u ∈ I' n, (emb u ∈ Call ∧ ∀ v : ↥SK, bS u v.1 ∈ Cst v.1) → (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs :=
      fun u hu h => ⟨hboxC u h.1, hQs_of n u hu h.2⟩
    have hUf_of : ∀ u ∈ I' n, (emb u ∈ Call ∧ ∀ v : ↥SK, bS u v.1 ∈ Cst v.1) → u ∈ Uf :=
      fun u hu h => hUf_mem u hu (hboxC u h.1) (hβ_ofS u (hQs_of n u hu h.2))

    have halg2 : ∀ (s : Finset ↥Ξ) (v : ↥SK) (k : ℕ) (w0 : ↥Ξ → ℂ)
        (wc : (v.1.adicCompletion K)ˣ → (v.1.adicCompletion K)ˣ → ↥Ξ → ℂ) (cc : (v.1.adicCompletion K)ˣ → (v.1.adicCompletion K)ˣ → ℂ) (t r : ℂ),
        t * (c' * ∑ ξ ∈ s, r * (w0 ξ + ∑ a ∈ Fa v.1, ∑ b ∈ Ft v.1 k, cc a b * wc a b ξ)) =
          t * (c' * ∑ ξ ∈ s, r * w0 ξ) + ∑ a ∈ Fa v.1, ∑ b ∈ Ft v.1 k, t * (c' * ∑ ξ ∈ s, r * (cc a b * wc a b ξ)) := by
      intro s v k w0 wc cc t r
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
    have halg3 : ∀ (s : Finset ↥Ξ) (A : ↥Ξ → ℂ) (D : ↥SK → ↥Ξ → ℂ) (r : ↥SK → ℂ) (t : ℂ),
        t * (c' * ∑ ξ ∈ s, (A ξ + ∑ v : ↥SK, r v * D v ξ)) = t * (c' * ∑ ξ ∈ s, A ξ) + ∑ v : ↥SK, t * (c' * ∑ ξ ∈ s, r v * D v ξ) := by
      intro s A D r t
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    have hterm_dec : ∀ u ∈ I' n, (u : K) ≠ 1 →
        term n u = gA n u + ∑ v : ↥SK, (g0 n v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, gc n v k α τ u) := by
      intro u huI hu
      have hterm : term n u = tilt n * (c' * ∑ ξ : ↥Ξ, WD ξ.1 u) := by
        simp only [term]
        rw [← Finset.sum_coe_sort]
      have hWD' : ∀ ξ : ↥Ξ, WD ξ.1 u = (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ.1 ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (ARCH u zS * ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) +
          ∑ v : ↥SK, ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ) * ∫ zS, DI ξ v.1 u zS ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) := by
        intro ξ
        rw [hWD u hu ξ, ← Finset.sum_coe_sort SK]
      rw [hterm]
      simp only [hWD']
      rw [halg3 Finset.univ _ (fun v ξ => ∫ zS, DI ξ v.1 u zS ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) (fun v => ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ)) (tilt n)]
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      rcases em (∃ k, (uv u v.1)⁻¹ ∈ sh v.1 k) with ⟨k₀, hk₀⟩ | hno
      ·
        have hk₀' : (Units.map (AutomorphicForm.adelePlaceAlgHom K v.1).toRingHom.toMonoidHom (ιK u))⁻¹ ∈ sh v.1 k₀ := by
          rw [huvφ]; exact hk₀
        have hI : ∀ ξ : ↥Ξ, (∫ zS, DI ξ v.1 u zS ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
            Wf ξ (ΦF0 v.1) (emb u) (bS u) + ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k₀, cv v.1 k₀ α τ * Wf ξ (ΦFc v.1 k₀ α τ) (emb u) (bS u) :=
          fun ξ => (hDI_on v.1 v.2 k₀ u hk₀' ξ).2
        simp only [hI]
        rw [halg2 Finset.univ v k₀ (fun ξ => Wf ξ (ΦF0 v.1) (emb u) (bS u)) (fun α τ ξ => Wf ξ (ΦFc v.1 k₀ α τ) (emb u) (bS u))
          (cv v.1 k₀) (tilt n) _]
        congr 1
        have hgc_k₀ : ∀ α τ, gc n v k₀ α τ u = tilt n * (c' * ∑ ξ : ↥Ξ, ((Real.sqrt ‖bS u v.1‖ : ℝ) : ℂ) *
            (cv v.1 k₀ α τ * Wf ξ (ΦFc v.1 k₀ α τ) (emb u) (bS u))) := fun α τ => by simp only [gc, if_pos hk₀]
        have hgc_ne : ∀ k, k ≠ k₀ → ∀ α τ, gc n v k α τ u = 0 := by
          intro k hk α τ
          have : (uv u v.1)⁻¹ ∉ sh v.1 k := fun h => hk (hshell_unique v _ k k₀ h hk₀)
          simp only [gc, if_neg this]
        have hsumK : ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, gc n v k α τ u =
            ∑ k ∈ Kall, (if k₀ = k then ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k₀, gc n v k₀ α τ u else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : k₀ = k
          · subst hk; rw [if_pos rfl]
          · rw [if_neg hk]
            exact Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun τ _ => hgc_ne k (Ne.symm hk) α τ
        rw [hsumK, Finset.sum_ite_eq]
        by_cases hK : k₀ ∈ Kall
        · rw [if_pos hK]
          exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun τ _ => (hgc_k₀ α τ).symm
        · rw [if_neg hK]
          refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun τ hτ => ?_
          rw [← hgc_k₀]
          by_contra hne
          exact hK (hKall u (hUf_of u huI (hsuppc n v k₀ α hα τ hτ u hne).1) v k₀ (hsuppc n v k₀ α hα τ hτ u hne).2.1)
      ·
        have hno' : ∀ k, (Units.map (AutomorphicForm.adelePlaceAlgHom K v.1).toRingHom.toMonoidHom (ιK u))⁻¹ ∉ sh v.1 k := by
          intro k hk; rw [huvφ] at hk; exact hno ⟨k, hk⟩
        have hI : ∀ ξ : ↥Ξ, (∫ zS, DI ξ v.1 u zS ∂(Measure.map (NumberField.Idele.partAt K SK) (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) = Wf ξ (ΦF0 v.1) (emb u) (bS u) :=
          fun ξ => (hDI_off v.1 v.2 u hno' ξ).2
        simp only [hI]
        have hgc0 : ∀ k α τ, gc n v k α τ u = 0 := by
          intro k α τ
          simp only [gc, if_neg (fun h => hno ⟨k, h⟩)]
        simp only [hgc0, Finset.sum_const_zero, add_zero, g0]

    let pA : Kˣ → ℂ := fun u => if (u : K) = 1 then 0 else C * gA n u
    let p0 : ↥SK → Kˣ → ℂ := fun v u => if (u : K) = 1 then 0 else C * g0 n v u
    let pc : (v : ↥SK) → ℕ → (v.1.adicCompletion K)ˣ → (v.1.adicCompletion K)ˣ → Kˣ → ℂ :=
      fun v k α τ u => if (u : K) = 1 then 0 else C * gc n v k α τ u
    have hpA_supp : ∀ u ∈ I' n, pA u ≠ 0 → (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs := by
      intro u hu hne
      by_cases h1 : (u : K) = 1
      · exact absurd (by simp only [pA, if_pos h1]) hne
      · have : gA n u ≠ 0 := fun h => hne (by simp only [pA, if_neg h1, h, mul_zero])
        exact hQs_piece u hu (hsuppA n u h1 this)
    have hp0_supp : ∀ (v : ↥SK), ∀ u ∈ I' n, p0 v u ≠ 0 → (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs := by
      intro v u hu hne
      by_cases h1 : (u : K) = 1
      · exact absurd (by simp only [p0, if_pos h1]) hne
      · have : g0 n v u ≠ 0 := fun h => hne (by simp only [p0, if_neg h1, h, mul_zero])
        exact hQs_piece u hu (hsupp0 n v u this)
    have hpc_supp : ∀ (v : ↥SK) (k : ℕ), ∀ α ∈ Fa v.1, ∀ τ ∈ Ft v.1 k, ∀ u ∈ I' n, pc v k α τ u ≠ 0 →
        (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs := by
      intro v k α hα τ hτ u hu hne
      by_cases h1 : (u : K) = 1
      · exact absurd (by simp only [pc, if_pos h1]) hne
      · have : gc n v k α τ u ≠ 0 := fun h => hne (by simp only [pc, if_neg h1, h, mul_zero])
        exact hQs_piece u hu (hsuppc n v k α hα τ hτ u this).1

    have hS1 : C * ∑ᶠ u ∈ In n, term n u =
        ∑ᶠ u ∈ I' n, (pA u + ∑ v : ↥SK, (p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u)) := by
      rw [hII' n, mul_finsum_mem]
      refine finsum_mem_congr rfl fun u hu => ?_
      by_cases h1 : (u : K) = 1
      · have hu1 : u = 1 := Units.ext h1
        subst hu1
        simp only [hterm1, mul_zero, pA, p0, pc, if_pos h1, Finset.sum_const_zero, add_zero]
      · rw [hterm_dec u hu h1]
        simp only [pA, p0, pc, if_neg h1, mul_add, Finset.mul_sum]

    have hfin_sum : ∀ (X : Type) (s : Finset X) (F : X → Kˣ → ℂ), (∀ x ∈ s, (I' n ∩ Function.support (F x)).Finite) →
        (I' n ∩ Function.support (fun u => ∑ x ∈ s, F x u)).Finite := by
      intro X s F h
      refine (Set.Finite.biUnion (Finset.finite_toSet s) fun x hx => h x hx).subset ?_
      rintro u ⟨huI, hu⟩
      obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
      exact Set.mem_biUnion hx ⟨huI, hne⟩
    have hfsum : ∀ (X : Type) (s : Finset X) (F : X → Kˣ → ℂ), (∀ x ∈ s, (I' n ∩ Function.support (F x)).Finite) →
        ∑ᶠ u ∈ I' n, ∑ x ∈ s, F x u = ∑ x ∈ s, ∑ᶠ u ∈ I' n, F x u := by
      intro X s F h
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        have hx' : (I' n ∩ Function.support (F x)).Finite := h x (Finset.mem_insert_self x s)
        have hs' : ∀ y ∈ s, (I' n ∩ Function.support (F y)).Finite := fun y hy => h y (Finset.mem_insert_of_mem hy)
        rw [Finset.sum_insert hx, ← ih hs', ← finsum_mem_add_distrib' hx' (hfin_sum X s F hs')]
        exact finsum_mem_congr rfl fun u _ => Finset.sum_insert hx
    have hfinA : (I' n ∩ Function.support pA).Finite := hSfinG n pA hpA_supp
    have hfin0 : ∀ v : ↥SK, (I' n ∩ Function.support (p0 v)).Finite := fun v => hSfinG n (p0 v) (hp0_supp v)
    have hfinc : ∀ (v : ↥SK) (k : ℕ), ∀ α ∈ Fa v.1, ∀ τ ∈ Ft v.1 k, (I' n ∩ Function.support (pc v k α τ)).Finite :=
      fun v k α hα τ hτ => hSfinG n (pc v k α τ) (hpc_supp v k α hα τ hτ)
    have hS2 : ∑ᶠ u ∈ I' n, (pA u + ∑ v : ↥SK, (p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u)) =
        ∑ᶠ u ∈ I' n, pA u + ∑ v : ↥SK, (∑ᶠ u ∈ I' n, p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, ∑ᶠ u ∈ I' n, pc v k α τ u) := by
      have hfc3 : ∀ (v : ↥SK) (k : ℕ), ∀ α ∈ Fa v.1, (I' n ∩ Function.support (fun u => ∑ τ ∈ Ft v.1 k, pc v k α τ u)).Finite :=
        fun v k α hα => hfin_sum _ _ (fun τ => pc v k α τ) (fun τ hτ => hfinc v k α hα τ hτ)
      have hfc2 : ∀ (v : ↥SK), ∀ k ∈ Kall, (I' n ∩ Function.support (fun u => ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u)).Finite :=
        fun v k _ => hfin_sum _ _ (fun α u => ∑ τ ∈ Ft v.1 k, pc v k α τ u) (fun α hα => hfc3 v k α hα)
      have hfc1 : ∀ v : ↥SK, (I' n ∩ Function.support (fun u => ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u)).Finite :=
        fun v => hfin_sum _ _ (fun k u => ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u) (fun k hk => hfc2 v k hk)
      have hfv : ∀ v : ↥SK, (I' n ∩ Function.support (fun u => p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u)).Finite := by
        intro v
        refine ((hfin0 v).union (hfc1 v)).subset ?_
        rintro u ⟨huI, hu⟩
        rw [Function.mem_support] at hu
        by_cases h : p0 v u = 0
        · right; refine ⟨huI, ?_⟩; rw [Function.mem_support]; intro h'; apply hu; rw [h, h', add_zero]
        · left; exact ⟨huI, h⟩
      have hfV : (I' n ∩ Function.support (fun u => ∑ v : ↥SK, (p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u))).Finite :=
        hfin_sum _ _ (fun v u => p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u) (fun v _ => hfv v)
      rw [finsum_mem_add_distrib' hfinA hfV, hfsum _ _ (fun v u => p0 v u + ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u) (fun v _ => hfv v)]
      congr 1
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [finsum_mem_add_distrib' (hfin0 v) (hfc1 v), hfsum _ _ (fun k u => ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, pc v k α τ u) (fun k hk => hfc2 v k hk)]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hfsum _ _ (fun α u => ∑ τ ∈ Ft v.1 k, pc v k α τ u) (fun α hα => hfc3 v k α hα)]
      refine Finset.sum_congr rfl fun α hα => ?_
      exact hfsum _ _ (fun τ => pc v k α τ) (fun τ hτ => hfinc v k α hα τ hτ)

    have hI₀sum : ∀ Φ : ↥hBfinS.toFinset → Kˣ → Fin nCs → ℂ,
        ∑ β : ↥hBfinS.toFinset, ∑ z ∈ hμfin.toFinset, ∑ j : Fin nCs, Φ β z j = ∑ i : I₀, Φ i.1 (i.2.1 : Kˣ) i.2.2 := by
      intro Φ
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort]
    have hsplitP : ∀ (piece : Kˣ → ℂ),
        (∀ u ∈ I' n, (if ((u : Kˣ) : K) = 1 then (0 : ℂ) else C * piece u) ≠ 0 → (∀ i, |(Log u).1 i| ≤ R₀) ∧ u ∈ Qs) →
        ∑ᶠ u ∈ I' n, (if (u : K) = 1 then 0 else C * piece u) =
          ∑ i : I₀, ∑ᶠ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then piece (urep i * g) else 0) := by
      intro piece hp
      rw [hsplitG n _ hp, hI₀sum]
      refine Finset.sum_congr rfl fun i _ => finsum_mem_congr rfl fun g _ => ?_
      have hrew : ubS i.1 * ((i.2.1 : Kˣ) * cCs i.2.2 * g) = urep i * g := by
        simp only [urep, mul_assoc]
      rw [hrew]
      by_cases hI : urep i * g ∈ I' n
      · by_cases h1 : ((urep i * g : Kˣ) : K) = 1
        · rw [if_pos hI, if_pos h1, if_neg (fun h => h.2 h1), mul_zero]
        · rw [if_pos hI, if_neg h1, if_pos ⟨hI, h1⟩]
      · rw [if_neg hI, if_neg (fun h => hI h.1), mul_zero]

    let STg : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → (Fin T.card → ℤ) → (((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ) → ℂ :=
      fun S x₀ θ₀ n₀ Kf => ∑' γ : S, (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ = n then
        Kf (x₀ + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0)
    let ST : Ty → ℂ := fun t => STg (subT t) (x₀T t) (θ₀T t) (n₀T t) (KS (shapeR (Sum.elim id id t)))
    let FT : Ty → ℂ := fun t => lamT t * ST t
    let RT : TyR → ℂ := fun r => FT (Sum.inl r) + FT (Sum.inr r)
    have hTYPE' : ∀ (H' : Subgroup Kˣ) (hH' : H' ≤ FA) (u : Kˣ) (piece : Kˣ → ℂ)
        (Kf : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) → ℂ) (Rb : ℝ), (∀ p : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), (∃ i, Rb < |p.1 i|) → Kf p = 0) →
        ∀ (lam : ℂ) (x₀ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ)) (θ₀ : (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (n₀ : (Fin T.card → ℤ)),
        (∀ g ∈ H', ((u * g : Kˣ) : K) ≠ 1 → C * (if u * g ∈ I' n then piece (u * g) else 0) =
            lam * (if (Lmap g).2 + n₀ = n then Kf (x₀ + (Lmap g).1, θ₀ + lift (Lmap g)) else 0)) →
        ∑ᶠ g ∈ (H' : Set Kˣ), C * (if u * g ∈ I' n ∧ ((u * g : Kˣ) : K) ≠ 1 then piece (u * g) else 0) =
          lam * STg (SL H' hH') x₀ θ₀ n₀ Kf +
          (-(lam * @ite ℂ (u⁻¹ ∈ H') (Classical.dec _) 1 0)) * STg ⊥ (x₀ + (Lmap u⁻¹).1) (θ₀ + lift (Lmap u⁻¹)) (n₀ + (Lmap u⁻¹).2) Kf :=
      fun H' hH' u piece Kf Rb hKb lam x₀ θ₀ n₀ hpt => hTYPE n H' hH' u piece Kf Rb hKb lam x₀ θ₀ n₀ hpt
    have hRT_unfold : ∀ r : TyR, RT r = lamT (Sum.inl r) * STg (subT (Sum.inl r)) (x₀T (Sum.inl r)) (θ₀T (Sum.inl r)) (n₀T (Sum.inl r)) (KS (shapeR r)) +
        lamT (Sum.inr r) * STg (subT (Sum.inr r)) (x₀T (Sum.inr r)) (θ₀T (Sum.inr r)) (n₀T (Sum.inr r)) (KS (shapeR r)) := by
      intro r
      simp only [RT, FT, ST, Sum.elim_inl, Sum.elim_inr, id]

    have tA : ∀ i : I₀,
        lamT (Sum.inl (Sum.inl (Sum.inl i))) = 1 ∧ subT (Sum.inl (Sum.inl (Sum.inl i))) = SL Hs hHsFA ∧
        x₀T (Sum.inl (Sum.inl (Sum.inl i))) = (Log (urep i)).1 ∧ θ₀T (Sum.inl (Sum.inl (Sum.inl i))) = θ₀v (urep i) ∧
        n₀T (Sum.inl (Sum.inl (Sum.inl i))) = n₀f (urep i) ∧ KS (shapeR (Sum.inl (Sum.inl i))) = KA i ∧
        lamT (Sum.inr (Sum.inl (Sum.inl i))) = -(1 * @ite ℂ ((urep i)⁻¹ ∈ Hs) (Classical.dec _) 1 0) ∧
        subT (Sum.inr (Sum.inl (Sum.inl i))) = ⊥ ∧
        x₀T (Sum.inr (Sum.inl (Sum.inl i))) = (Log (urep i)).1 + (Lmap (urep i)⁻¹).1 ∧
        θ₀T (Sum.inr (Sum.inl (Sum.inl i))) = θ₀v (urep i) + lift (Lmap (urep i)⁻¹) ∧
        n₀T (Sum.inr (Sum.inl (Sum.inl i))) = n₀f (urep i) + (Lmap (urep i)⁻¹).2 := by
      intro i
      refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;>
        simp only [x₀T, x₀R, θ₀T, θ₀R, n₀T, n₀R, baseT, Sum.elim_inl, Sum.elim_inr]
    have t0 : ∀ (i : I₀) (v : ↥SK),
        lamT (Sum.inl (Sum.inl (Sum.inr (i, v)))) = ((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ) ∧
        subT (Sum.inl (Sum.inl (Sum.inr (i, v)))) = SL Hs hHsFA ∧
        x₀T (Sum.inl (Sum.inl (Sum.inr (i, v)))) = (Log (urep i)).1 ∧ θ₀T (Sum.inl (Sum.inl (Sum.inr (i, v)))) = θ₀v (urep i) ∧
        n₀T (Sum.inl (Sum.inl (Sum.inr (i, v)))) = n₀f (urep i) ∧ KS (shapeR (Sum.inl (Sum.inr (i, v)))) = G0 i v ∧
        lamT (Sum.inr (Sum.inl (Sum.inr (i, v)))) = -(((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ) * @ite ℂ ((urep i)⁻¹ ∈ Hs) (Classical.dec _) 1 0) ∧
        subT (Sum.inr (Sum.inl (Sum.inr (i, v)))) = ⊥ ∧
        x₀T (Sum.inr (Sum.inl (Sum.inr (i, v)))) = (Log (urep i)).1 + (Lmap (urep i)⁻¹).1 ∧
        θ₀T (Sum.inr (Sum.inl (Sum.inr (i, v)))) = θ₀v (urep i) + lift (Lmap (urep i)⁻¹) ∧
        n₀T (Sum.inr (Sum.inl (Sum.inr (i, v)))) = n₀f (urep i) + (Lmap (urep i)⁻¹).2 := by
      intro i v
      have e6 : KS (shapeR (Sum.inl (Sum.inr (i, v)))) = G0 i v := funext fun p => hKS_0 i v p
      refine ⟨rfl, rfl, ?_, ?_, ?_, e6, rfl, rfl, ?_, ?_, ?_⟩ <;>
        simp only [x₀T, x₀R, θ₀T, θ₀R, n₀T, n₀R, baseT, Sum.elim_inl, Sum.elim_inr]
    have tC : ∀ (i : I₀) (v : ↥SK) (k a t : ℕ),
        lamT (Sum.inl (Sum.inr (((i, v), k), (a, t)))) = lamC i v k a t ∧
        subT (Sum.inl (Sum.inr (((i, v), k), (a, t)))) = SL (Hvk v k) (hHvk_FA v k) ∧
        x₀T (Sum.inl (Sum.inr (((i, v), k), (a, t)))) = (Log (urep i)).1 + (Lmap (δf i v k (τOf v k t))).1 ∧
        θ₀T (Sum.inl (Sum.inr (((i, v), k), (a, t)))) = θ₀v (urep i) + lift (Lmap (δf i v k (τOf v k t))) ∧
        n₀T (Sum.inl (Sum.inr (((i, v), k), (a, t)))) = n₀f (urep i) + (Lmap (δf i v k (τOf v k t))).2 ∧
        KS (shapeR (Sum.inr (((i, v), k), (a, t)))) = KS (shapeC i v a) ∧
        lamT (Sum.inr (Sum.inr (((i, v), k), (a, t)))) = -(lamC i v k a t * @ite ℂ ((urep i * δf i v k (τOf v k t))⁻¹ ∈ Hvk v k) (Classical.dec _) 1 0) ∧
        subT (Sum.inr (Sum.inr (((i, v), k), (a, t)))) = ⊥ ∧
        x₀T (Sum.inr (Sum.inr (((i, v), k), (a, t)))) = (Log (urep i)).1 + (Lmap (δf i v k (τOf v k t))).1 + (Lmap (urep i * δf i v k (τOf v k t))⁻¹).1 ∧
        θ₀T (Sum.inr (Sum.inr (((i, v), k), (a, t)))) = θ₀v (urep i) + lift (Lmap (δf i v k (τOf v k t))) + lift (Lmap (urep i * δf i v k (τOf v k t))⁻¹) ∧
        n₀T (Sum.inr (Sum.inr (((i, v), k), (a, t)))) = n₀f (urep i) + (Lmap (δf i v k (τOf v k t))).2 + (Lmap (urep i * δf i v k (τOf v k t))⁻¹).2 := by
      intro i v k a t
      refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;>
        simp only [x₀T, x₀R, θ₀T, θ₀R, n₀T, n₀R, baseT, δT, Sum.elim_inl, Sum.elim_inr]
    have hKA_box : ∀ (i : I₀) (p : ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ))), (∃ i', RbA i < |p.1 i'|) → KA i p = 0 := by
      intro i p hp
      obtain ⟨h1, h2, h3⟩ := hA_supp i p hp
      simp only [KA, h1, h2, h3, mul_zero, Finset.sum_const_zero, add_zero]

    have hRA : ∀ i : I₀, ∑ᶠ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gA n (urep i * g) else 0) =
        RT (Sum.inl (Sum.inl i)) := by
      intro i
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := tA i
      rw [hTYPE' Hs hHsFA (urep i) (gA n) (KA i) (RbA i) (hKA_box i) 1 ((Log (urep i)).1) (θ₀v (urep i)) (n₀f (urep i)) (hidA n i),
        hRT_unfold, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

    have hR0 : ∀ (i : I₀) (v : ↥SK), ∑ᶠ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then g0 n v (urep i * g) else 0) =
        RT (Sum.inl (Sum.inr (i, v))) := by
      intro i v
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := t0 i v
      rw [hTYPE' Hs hHsFA (urep i) (g0 n v) (G0 i v) (Rb0 i v) (hG0_supp i v) _ ((Log (urep i)).1) (θ₀v (urep i)) (n₀f (urep i)) (hid0 n i v),
        hRT_unfold, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

    have hcell_reidx : ∀ (i : I₀) (v : ↥SK) (k : ℕ), ∀ α ∈ Fa v.1, ∀ τ ∈ Ft v.1 k,
        (∃ g ∈ Hs, uv (urep i * g) v.1 * τ ∈ Vv v.1 k) →
        ∑ᶠ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k α τ (urep i * g) else 0) =
          ∑ᶠ g' ∈ (Hvk v k : Set Kˣ), C * (if urep i * δf i v k τ * g' ∈ I' n ∧ ((urep i * δf i v k τ * g' : Kˣ) : K) ≠ 1 then
            gc n v k α τ (urep i * δf i v k τ * g') else 0) := by
      intro i v k α hα τ hτ hfire
      obtain ⟨hδ, hδV⟩ := hδf i v k τ hfire
      let F : Kˣ → ℂ := fun g => C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k α τ (urep i * g) else 0)
      have hsupp : ∀ g ∈ (Hs : Set Kˣ), F g ≠ 0 → g ∈ (fun g' => δf i v k τ * g') '' (Hvk v k : Set Kˣ) := by
        intro g hg hne
        have hI : urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 := by
          by_contra h; apply hne; simp only [F, if_neg h, mul_zero]
        have hgc : gc n v k α τ (urep i * g) ≠ 0 := by
          intro h; apply hne; simp only [F, if_pos hI, h, mul_zero]
        have hV := (hsuppc n v k α hα τ hτ _ hgc).2.2
        refine ⟨(δf i v k τ)⁻¹ * g, ?_, by group⟩
        rw [SetLike.mem_coe, hHvk_mem]
        refine ⟨Hs.mul_mem (Hs.inv_mem hδ) hg, ?_⟩
        have hx : urep i * g = (urep i * δf i v k τ) * ((δf i v k τ)⁻¹ * g) := by group
        have h2 : uv (urep i * g) v.1 * τ = (uv (urep i * δf i v k τ) v.1 * τ) * uv ((δf i v k τ)⁻¹ * g) v.1 := by
          rw [hx, huv_mul (urep i * δf i v k τ), mul_right_comm]
        have h3 : uv ((δf i v k τ)⁻¹ * g) v.1 = (uv (urep i * δf i v k τ) v.1 * τ)⁻¹ * (uv (urep i * g) v.1 * τ) := by
          rw [h2, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [h3]
        exact (Vv v.1 k).mul_mem ((Vv v.1 k).inv_mem hδV) hV
      have hsub : (fun g' => δf i v k τ * g') '' (Hvk v k : Set Kˣ) ⊆ (Hs : Set Kˣ) := by
        rintro _ ⟨g', hg', rfl⟩
        exact Hs.mul_mem hδ (hHvk_Hs v k hg')
      have h1 : ∑ᶠ g ∈ (Hs : Set Kˣ), F g = ∑ᶠ g ∈ (fun g' => δf i v k τ * g') '' (Hvk v k : Set Kˣ), F g := by
        apply finsum_mem_inter_support_eq
        ext g
        constructor
        · rintro ⟨hg, hF⟩; exact ⟨hsupp g hg hF, hF⟩
        · rintro ⟨hg, hF⟩; exact ⟨hsub hg, hF⟩
      show ∑ᶠ g ∈ (Hs : Set Kˣ), F g = _
      rw [h1, finsum_mem_image (mul_right_injective (δf i v k τ)).injOn]
      refine finsum_mem_congr rfl fun g' _ => ?_
      simp only [F, mul_assoc]

    have hRc : ∀ (i : I₀) (v : ↥SK) (k a t : ℕ) (ha : a < (Fa v.1).card) (ht : t < (Ft v.1 k).card),
        ∑ᶠ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k (αOf v a) (τOf v k t) (urep i * g) else 0) =
        RT (Sum.inr (((i, v), k), (a, t))) := by
      intro i v k a t ha ht
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := tC i v k a t
      have hαOf : αOf v a = (((Fa v.1).equivFin.symm ⟨a, ha⟩ : ↥(Fa v.1)) : (v.1.adicCompletion K)ˣ) := by simp only [αOf, dif_pos ha]
      have hshC : shapeC i v a = (i, Sum.inr (Sum.inr ⟨v, (Fa v.1).equivFin.symm ⟨a, ha⟩⟩)) := by simp only [shapeC, dif_pos ha]
      rw [hRT_unfold, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, hshC]
      rw [show KS (i, Sum.inr (Sum.inr ⟨v, (Fa v.1).equivFin.symm ⟨a, ha⟩⟩)) = Gc i ⟨v, (Fa v.1).equivFin.symm ⟨a, ha⟩⟩ from
        funext fun p => hKS_c i _ p]
      rcases Classical.dec (fire i v k (τOf v k t)) with hfire | hfire
      ·
        have hlam : lamC i v k a t = 0 := by
          simp only [lamC, if_pos (And.intro ha ht)]
          rw [if_neg hfire]
        rw [hlam]
        simp only [zero_mul, neg_zero, zero_add, add_zero]
        have hz : ∀ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k (αOf v a) (τOf v k t) (urep i * g) else 0) = 0 := by
          intro g hg
          by_cases hI : urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1
          · rw [if_pos hI]
            by_contra hne
            have hgc : gc n v k (αOf v a) (τOf v k t) (urep i * g) ≠ 0 := fun h => hne (by rw [h, mul_zero])
            exact hfire ⟨g, hg, (hsuppc n v k _ (hαOf_mem v a ha) _ (hτOf_mem v k t ht) _ hgc).2.2⟩
          · rw [if_neg hI, mul_zero]
        rw [finsum_mem_congr (g := fun _ => (0 : ℂ)) rfl hz]
        simp
      ·
        have hlam : lamC i v k a t = (if τOf v k t ∈ sh v.1 k then 1 else 0) * ((Real.sqrt ‖bS (urep i) v.1‖ : ℝ) : ℂ) *
            cv v.1 k (αOf v a) (τOf v k t) := by
          simp only [lamC, if_pos (And.intro ha ht)]
          rw [if_pos hfire]
        rw [hcell_reidx i v k (αOf v a) (hαOf_mem v a ha) (τOf v k t) (hτOf_mem v k t ht) hfire, hlam]
        refine hTYPE' (Hvk v k) (hHvk_FA v k) (urep i * δf i v k (τOf v k t)) (gc n v k (αOf v a) (τOf v k t))
          (Gc i ⟨v, (Fa v.1).equivFin.symm ⟨a, ha⟩⟩) (Rbc i _) (hGc_supp i _) _ _ _ _ ?_
        intro g' hg' hne
        have := hidc n i v k ((Fa v.1).equivFin.symm ⟨a, ha⟩) (τOf v k t) hfire g' hg' hne
        rw [hαOf]
        exact this
    have hRc_inv : ∀ (i : I₀) (v : ↥SK) (k a t : ℕ), ¬(a < (Fa v.1).card ∧ t < (Ft v.1 k).card) → RT (Sum.inr (((i, v), k), (a, t))) = 0 := by
      intro i v k a t h
      obtain ⟨e1, -, -, -, -, -, e7, -⟩ := tC i v k a t
      have hlam : lamC i v k a t = 0 := by simp only [lamC, if_neg h]
      rw [hRT_unfold, e1, e7, hlam]
      simp
    have hRc_K : ∀ (i : I₀) (v : ↥SK) (k a t : ℕ), a < (Fa v.1).card → t < (Ft v.1 k).card → k ∉ Kall →
        RT (Sum.inr (((i, v), k), (a, t))) = 0 := by
      intro i v k a t ha ht hk
      rw [← hRc i v k a t ha ht]
      have hz : ∀ g ∈ (Hs : Set Kˣ), C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k (αOf v a) (τOf v k t) (urep i * g) else 0) = 0 := by
        intro g hg
        by_cases hI : urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1
        · rw [if_pos hI]
          by_contra hne
          have hgc : gc n v k (αOf v a) (τOf v k t) (urep i * g) ≠ 0 := fun h => hne (by rw [h, mul_zero])
          have hs := hsuppc n v k _ (hαOf_mem v a ha) _ (hτOf_mem v k t ht) _ hgc
          exact hk (hKall _ (hUf_of _ hI.1 hs.1) v k hs.2.1)
        · rw [if_neg hI, mul_zero]
      rw [finsum_mem_congr (g := fun _ => (0 : ℂ)) rfl hz]
      simp

    let Fo : Option Ty → ℂ := fun o => o.elim 0 lamT * ∑' γ : ↥(o.elim (⊥ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) subT),
      (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + o.elim 0 n₀T = n then
        KF (BwF (o.elim (Fin.last A₀) (fun t => (shapeT t).castSucc))) (CwF (o.elim (Fin.last A₀) (fun t => (shapeT t).castSucc)))
          (EwF (o.elim (Fin.last A₀) (fun t => (shapeT t).castSucc)))
          (o.elim 0 x₀T + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, o.elim 0 θ₀T + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0)
    have hFo_none : Fo none = 0 := by simp only [Fo, Option.elim_none, zero_mul]
    have hFo_some : ∀ t : Ty, Fo (some t) = FT t := by
      intro t
      simp only [Fo, Option.elim_some, FT, ST, STg, shapeT, hBwF_c, hCwF_c, hEwF_c, Equiv.symm_apply_apply, ← hKS_KF]
    have hRHS1 : (∑' i : ℕ, lamN i * ∑' γ : subN i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀N i = n then
            BwF (shapeN i) (x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ k : Fin (Fintype.card {w : InfinitePlace K // w.IsReal}), ((|1 - Real.exp ((x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kR k))| : ℝ) : ℂ) * CwF (shapeN i) k (x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) +
              ∑ j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card), ((‖(1 : ℂ) - Complex.exp ((((x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                    Real.log ‖(1 : ℂ) - Complex.exp ((((x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
                EwF (shapeN i) j (x₀N i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀N i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0) = ∑' m : ℕ, Fo (dec m) := rfl
    have hRHS2 : ∑' m : ℕ, Fo (dec m) = ∑' t : Ty, FT t := by
      have hsupp : Function.support (fun m : ℕ => Fo (dec m)) ⊆ Set.range (Encodable.encode : Ty → ℕ) := by
        intro m hm
        by_contra h
        rw [Function.mem_support, hdec_none m h, hFo_none] at hm
        exact hm rfl
      rw [← (Encodable.encode_injective (α := Ty)).tsum_eq hsupp]
      refine tsum_congr fun t => ?_
      show Fo (dec (Encodable.encode t)) = FT t
      rw [hdec_enc, hFo_some]

    have hghost_cell : ∀ c : TyC, FT (Sum.inr (Sum.inr c)) = 0 := by
      rintro ⟨⟨⟨i, v⟩, k⟩, ⟨a, t⟩⟩
      show lamT (Sum.inr (Sum.inr (((i, v), k), (a, t)))) * ST _ = 0
      rw [show lamT (Sum.inr (Sum.inr (((i, v), k), (a, t)))) =
        -(lamC i v k a t * @ite ℂ ((urep i * δf i v k (τOf v k t))⁻¹ ∈ Hvk v k) (Classical.dec _) 1 0) from rfl]
      rcases Classical.dec ((urep i * δf i v k (τOf v k t))⁻¹ ∈ Hvk v k) with hm | hm
      · rw [if_neg hm]; simp
      · suffices hl : lamC i v k a t = 0 by rw [hl]; simp
        simp only [lamC]
        by_cases hval : a < (Fa v.1).card ∧ t < (Ft v.1 k).card
        · rw [if_pos hval]
          rcases Classical.dec (fire i v k (τOf v k t)) with hf | hf
          · rw [if_neg hf]
          · rw [if_pos hf]
            have hτV : τOf v k t ∈ Vv v.1 k := by
              obtain ⟨hδ, hδV⟩ := hδf i v k (τOf v k t) hf
              have h2 := ((hHvk_mem v k _).1 hm).2
              simp only [uv, map_inv] at h2
              have := (Vv v.1 k).mul_mem h2 hδV
              simp only [uv] at this
              rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
            have : τOf v k t ∉ sh v.1 k := fun h => hsh_V v.1 v.2 k _ h hτV
            rw [if_neg this, zero_mul, zero_mul]
        · rw [if_neg hval]

    let CF : Finset TyC := ((Finset.univ : Finset (I₀ × ↥SK)) ×ˢ Kall) ×ˢ (Finset.range Amax ×ˢ Finset.range Mmax)
    have hCF_zero : ∀ c : TyC, c ∉ CF → RT (Sum.inr c) = 0 := by
      rintro ⟨⟨⟨i, v⟩, k⟩, ⟨a, t⟩⟩ hc
      by_cases hval : a < (Fa v.1).card ∧ t < (Ft v.1 k).card
      · by_cases hk : k ∈ Kall
        · exact absurd (Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, hk⟩,
            Finset.mem_product.2 ⟨Finset.mem_range.2 (lt_of_lt_of_le hval.1 (hAmax v)),
              Finset.mem_range.2 (lt_of_lt_of_le hval.2 (hMmax v k))⟩⟩) hc
        · exact hRc_K i v k a t hval.1 hval.2 hk
      · exact hRc_inv i v k a t hval
    let SRfin : Finset TyR := (Finset.univ : Finset (I₀ ⊕ (I₀ × ↥SK))).image Sum.inl ∪ CF.image Sum.inr
    have hSR_zero : ∀ r : TyR, r ∉ SRfin → FT (Sum.inl r) = 0 ∧ FT (Sum.inr r) = 0 := by
      rintro (x | c) hr
      · exact absurd (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))) hr
      · have hc : c ∉ CF := fun h => hr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
        have h1 := hCF_zero c hc
        have h2 := hghost_cell c
        refine ⟨?_, h2⟩
        have : RT (Sum.inr c) = FT (Sum.inl (Sum.inr c)) + FT (Sum.inr (Sum.inr c)) := rfl
        rw [this, h2, add_zero] at h1
        exact h1
    have hsumL : Summable (fun r : TyR => FT (Sum.inl r)) :=
      summable_of_ne_finset_zero (s := SRfin) fun r hr => (hSR_zero r hr).1
    have hsumR : Summable (fun r : TyR => FT (Sum.inr r)) :=
      summable_of_ne_finset_zero (s := SRfin) fun r hr => (hSR_zero r hr).2
    have hRHS3 : ∑' t : Ty, FT t = ∑' r : TyR, RT r := by
      rw [Summable.tsum_sum (f := FT) hsumL hsumR, ← Summable.tsum_add hsumL hsumR]
    have hsumC : Summable (fun c : TyC => RT (Sum.inr c)) := summable_of_ne_finset_zero (s := CF) hCF_zero
    have hfinL : Summable (fun x : I₀ ⊕ (I₀ × ↥SK) => RT (Sum.inl x)) := Summable.of_finite
    have hRHS4 : ∑' r : TyR, RT r = ∑ x : I₀ ⊕ (I₀ × ↥SK), RT (Sum.inl x) + ∑ c ∈ CF, RT (Sum.inr c) := by
      rw [Summable.tsum_sum (f := RT) hfinL hsumC, tsum_fintype, tsum_eq_sum (s := CF) (fun c hc => hCF_zero c hc)]

    rw [hS1, hS2, hRHS1, hRHS2, hRHS3, hRHS4]
    rw [show (∑ᶠ u ∈ I' n, pA u) = ∑ i : I₀, RT (Sum.inl (Sum.inl i)) from by
      rw [hsplitP (gA n) hpA_supp]; exact Finset.sum_congr rfl fun i _ => hRA i]
    have h0v : ∀ v : ↥SK, ∑ᶠ u ∈ I' n, p0 v u = ∑ i : I₀, RT (Sum.inl (Sum.inr (i, v))) := by
      intro v; rw [hsplitP (g0 n v) (hp0_supp v)]; exact Finset.sum_congr rfl fun i _ => hR0 i v
    have hcv : ∀ (v : ↥SK), ∀ k ∈ Kall, ∀ α ∈ Fa v.1, ∀ τ ∈ Ft v.1 k,
        ∑ᶠ u ∈ I' n, pc v k α τ u = ∑ i : I₀, ∑ᶠ g ∈ (Hs : Set Kˣ),
          C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k α τ (urep i * g) else 0) :=
      fun v k hk α hα τ hτ => hsplitP (gc n v k α τ) (hpc_supp v k α hα τ hτ)
    simp only [h0v]
    rw [Fintype.sum_sum_type]

    have hinner : ∀ (i : I₀) (v : ↥SK) (k : ℕ), ∑ a ∈ Finset.range Amax, ∑ t ∈ Finset.range Mmax, RT (Sum.inr (((i, v), k), (a, t))) =
        ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, ∑ᶠ g ∈ (Hs : Set Kˣ),
          C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k α τ (urep i * g) else 0) := by
      intro i v k
      have hA : ∑ a ∈ Finset.range Amax, ∑ t ∈ Finset.range Mmax, RT (Sum.inr (((i, v), k), (a, t))) =
          ∑ a ∈ Finset.range (Fa v.1).card, ∑ t ∈ Finset.range (Ft v.1 k).card, RT (Sum.inr (((i, v), k), (a, t))) := by
        symm
        refine (Finset.sum_subset (Finset.range_subset_range.2 (hAmax v)) ?_).trans ?_
        · intro a _ ha
          rw [Finset.mem_range, not_lt] at ha
          exact Finset.sum_eq_zero fun t _ => hRc_inv i v k a t (fun h => (not_lt.2 ha) h.1)
        · refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_subset (Finset.range_subset_range.2 (hMmax v k)) ?_
          intro t _ ht
          rw [Finset.mem_range, not_lt] at ht
          exact hRc_inv i v k a t (fun h => (not_lt.2 ht) h.2)
      rw [hA, Finset.sum_range, ← Finset.sum_coe_sort (Fa v.1), ← Equiv.sum_comp (Fa v.1).equivFin.symm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_range, ← Finset.sum_coe_sort (Ft v.1 k), ← Equiv.sum_comp (Ft v.1 k).equivFin.symm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← hRc i v k a.1 t.1 a.2 t.2]
      have hαa : αOf v (a : ℕ) = (((Fa v.1).equivFin.symm a : ↥(Fa v.1)) : (v.1.adicCompletion K)ˣ) := by
        simp only [αOf, dif_pos a.2]
      have hτt : τOf v k (t : ℕ) = (((Ft v.1 k).equivFin.symm t : ↥(Ft v.1 k)) : (v.1.adicCompletion K)ˣ) := by
        simp only [τOf, dif_pos t.2]
      rw [hαa, hτt]
    have hcellsL : ∑ c ∈ CF, RT (Sum.inr c) = ∑ i : I₀, ∑ v : ↥SK, ∑ k ∈ Kall, ∑ a ∈ Finset.range Amax, ∑ t ∈ Finset.range Mmax,
        RT (Sum.inr (((i, v), k), (a, t))) := by
      show ∑ c ∈ ((Finset.univ : Finset (I₀ × ↥SK)) ×ˢ Kall) ×ˢ (Finset.range Amax ×ˢ Finset.range Mmax), RT (Sum.inr c) = _
      rw [Finset.sum_product, Finset.sum_product, ← @Finset.univ_product_univ I₀ ↥SK, Finset.sum_product]
      try simp only [Finset.sum_product]
    rw [hcellsL]
    have hcellsEq : ∑ i : I₀, ∑ v : ↥SK, ∑ k ∈ Kall, ∑ a ∈ Finset.range Amax, ∑ t ∈ Finset.range Mmax, RT (Sum.inr (((i, v), k), (a, t))) =
        ∑ v : ↥SK, ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, ∑ᶠ u ∈ I' n, pc v k α τ u := by
      have h1 : ∑ i : I₀, ∑ v : ↥SK, ∑ k ∈ Kall, ∑ a ∈ Finset.range Amax, ∑ t ∈ Finset.range Mmax, RT (Sum.inr (((i, v), k), (a, t))) =
          ∑ i : I₀, ∑ v : ↥SK, ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, ∑ᶠ g ∈ (Hs : Set Kˣ),
            C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k α τ (urep i * g) else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => hinner i v k
      have h2 : ∑ v : ↥SK, ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, ∑ᶠ u ∈ I' n, pc v k α τ u =
          ∑ v : ↥SK, ∑ k ∈ Kall, ∑ α ∈ Fa v.1, ∑ τ ∈ Ft v.1 k, ∑ i : I₀, ∑ᶠ g ∈ (Hs : Set Kˣ),
            C * (if urep i * g ∈ I' n ∧ ((urep i * g : Kˣ) : K) ≠ 1 then gc n v k α τ (urep i * g) else 0) :=
        Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun α hα =>
          Finset.sum_congr rfl fun τ hτ => hcv v k hk α hα τ hτ
      rw [h1, h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_comm]
    rw [hcellsEq]
    simp only [Finset.sum_add_distrib]
    have e2 : ∑ a₂ : I₀ × ↥SK, RT (Sum.inl (Sum.inr a₂)) = ∑ v : ↥SK, ∑ i : I₀, RT (Sum.inl (Sum.inr (i, v))) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [e2]
    ring
  refine ⟨A₀ + 1, Fintype.card {w : InfinitePlace K // w.IsReal}, Λ, hΛ_disc, sl, ω, hω, hpf, χ, lift, hcompat, kC, kR,
    BwF, CwF, EwF, ?_, ?_, ?_, ?_, Sx, hSx, ?_, subN, ?_, shapeN, lamN, ?_, x₀N, n₀N, θ₀N, fun n => hmain n⟩
  · intro a; refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [hBwF_l]; exact contDiff_const
    · rw [hBwF_c]; exact hBwS_sm _
  · intro a k'; refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [hCwF_l]; exact contDiff_const
    · rw [hCwF_c]; exact hCwS_sm _ _
  · intro a j; refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [hEwF_l]; exact contDiff_const
    · rw [hEwF_c]; exact hEwS_sm _ _
  · intro a p J; refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [hBwF_l, hCwF_l, hEwF_l]; exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
    · simp only [hBwF_c, hCwF_c, hEwF_c]; exact hS_per _ p J
  · intro a p hp; refine Fin.lastCases ?_ (fun a => ?_) a
    · simp only [hBwF_l, hCwF_l, hEwF_l]; exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
    · simp only [hBwF_c, hCwF_c, hEwF_c]; exact hS_supp _ p hp
  · intro m
    simp only [subN]
    cases dec m with
    | none => exact bot_le
    | some t => exact hsubT_le t
  · have h0 : ∀ m ∉ Set.range (Encodable.encode : Ty → ℕ), (fun m => ‖lamN m‖) m = 0 := fun m hm => by
      simp only [lamN, hdec_none m hm, Option.elim, norm_zero]
    refine ((Encodable.encode_injective).summable_iff h0).1 ?_
    refine hlamT_summ.congr fun t => ?_
    simp only [Function.comp_apply, lamN, hdec_enc, Option.elim]

end S_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le
end P2MW
export P2MW.S_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_discWindow_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_forall_eq_of_norm_sub_le (solution)
