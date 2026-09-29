-- Prove2me | solution 1 for NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5c865819-e1c7-52b7-9136-f176035dc6b4

import Definitions.Def_AutomorphicForm_TwistedOrbital
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
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

    (C c' : ℂ) :
    ∃ (N : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (sub : Fin N → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (G : Fin N → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) ∧
      ∃ (Rb : ℝ), 0 ≤ Rb ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), (∃ k, Rb < |p.1 k|) → G i p = 0) ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)), G i (p.1, p.2 + Pi.single j 1) = G i p) ∧
      ∃ (x₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : Fin N → Fin T.card → ℤ) (θ₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
        C *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (f (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (c' * ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
                (Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                        (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                      InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
                  ∏ v ∈ SK, Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
                      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                    (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
                ∂(Measure.map (NumberField.Idele.partAt K SK)
                  (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        ∑ i : Fin N, ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            G i (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by
  classical

  rcases Finset.eq_empty_or_nonempty Ξ with hΞ | ⟨ξ₀, hξ₀⟩
  · have hT0 : 0 < T.card := by omega
    refine ⟨0, ⊥, ?_, 0, fun _ => 1, ?_, ?_, 0, fun _ => 0, ?_, Fin.elim0, fun i => i.elim0, Fin.elim0,
      fun i => i.elim0, 0, le_rfl, fun i => i.elim0, fun i => i.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun n => ?_⟩
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
    · subst hΞ
      simp

  obtain ⟨Λf, Log, hLog, hLog_mul, hΛf_mem, hΛf_disc, hΛf_pf, hΛf_ω⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul K T f hf
  obtain ⟨Λ₁, Log₁, hLog₁, hLog₁_mul, hΛ₁_mem, hΛ₁_disc, hΛ₁_pf, hΛ₁_tors⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul K T
  have hLog₁eq : ∀ u, Log₁ u = Log u := fun u => by rw [hLog, hLog₁]
  obtain ⟨F, hF_T, hF_tors, hF_dec, hF_classes⟩ :=
    NumberField.exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen K T
  obtain ⟨P, sgn, arg, hP_smooth, hP_per, hP_mul, hP_norm, hP_inv, hP_sgnarg, hP_bdd⟩ :=
    NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_div_mult_polarCoord_units K
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

  let Wint : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → mixedEmbedding.mixedSpace K →
      ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) → ℂ := fun ξ x b =>
    ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
          ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
      ∂(Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))
  let ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
  let emb : Kˣ → mixedEmbedding.mixedSpace K := fun u =>
    InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))
  let bS : Kˣ → ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) := fun u v =>
    (((ιK u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
  let tvec : Fin T.card → ℂ := fun i => ((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1)
  let tilt : (Fin T.card → ℤ) → ℂ := fun n => ∏ i : Fin T.card, tvec i ^ (-(n i))
  let term : (Fin T.card → ℤ) → Kˣ → ℂ := fun n u => tilt n * (c' * ∑ ξ ∈ Ξ, Wint ξ (emb u) (bS u))
  have hemb : ∀ u : Kˣ, emb u = NumberField.mixedEmbedding K (u : K) := fun u => NumCore.emb_eq K u
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

  let C₀ : Set (mixedEmbedding.mixedSpace K) :=
    (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) '' Ca
  have hC₀ : IsCompact C₀ :=
    hCa.image ((NumCore.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.comp continuous_fst))
  have hC₀u : ∀ y ∈ C₀, IsUnit y := by
    rintro _ ⟨q, -, rfl⟩
    exact q.1.isUnit.map _
  have hWint0 : ∀ ξ (x : mixedEmbedding.mixedSpace K) b, Wint ξ x b ≠ 0 → x ∈ C₀ := by
    intro ξ x b hne
    by_contra hx
    apply hne
    have hzero : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] = 0 := by
      intro zS
      by_contra hΦ
      obtain ⟨q, hq, hpq⟩ := hΦa_Ca _ (subset_tsupport _ (Function.mem_support.2 hΦ))
      have h0 := congr_fun hpq 0
      simp only [Matrix.cons_val_zero] at h0
      exact hx ⟨q, hq, h0.symm⟩
    simp only [Wint, hzero, mul_zero, zero_mul, integral_zero]

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
  have hHFA : H ≤ FA := fun h hh => Subgroup.mem_inf.2 ⟨hHF hh, hHA hh⟩
  let sub₀ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    { carrier := {γ | ∃ h ∈ H, Lmap h = γ}
      zero_mem' := ⟨1, H.one_mem, hL_one⟩
      add_mem' := by
        rintro a b ⟨h, hh, rfl⟩ ⟨h', hh', rfl⟩
        exact ⟨h * h', H.mul_mem hh hh', hL_add h (hHFA hh) h' (hHFA hh')⟩
      neg_mem' := by
        rintro a ⟨h, hh, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, hL_inv h (hHFA hh)⟩ }
  have hsub₀_mem : ∀ γ, γ ∈ sub₀ ↔ ∃ h ∈ H, Lmap h = γ := fun γ => Iff.rfl
  have hsub₀Λ : sub₀ ≤ Λ := by
    rintro γ ⟨h, hh, rfl⟩
    exact (hΛ' _).2 ⟨h, hHFA hh, rfl⟩

  let cs : Fin (NumberField.InfinitePlace.nrComplexPlaces K) → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) :=
    fun j => Fin.castAdd T.card (Fintype.equivFin (NumberField.InfinitePlace K)
      ((Fintype.equivFin {w : NumberField.InfinitePlace K // w.IsComplex}).symm j).1)
  let ts : Fin T.card → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) :=
    fun j => Fin.natAdd (Fintype.card (NumberField.InfinitePlace K)) j

  let WaC : Kˣ → mixedEmbedding.mixedSpace K → ℂ := fun u x => C * (c' * ∑ ξ ∈ Ξ, Wint ξ x (bS u))
  have hWaC_smooth : ∀ u, ContDiff ℝ (⊤ : ℕ∞) (WaC u) := by
    intro u
    refine contDiff_const.mul (contDiff_const.mul ?_)
    exact ContDiff.sum fun ξ hξ => (hR4 ξ hξ).1 (bS u)
  have hWaC0 : ∀ u y, WaC u y ≠ 0 → y ∈ C₀ := by
    intro u y hy
    have : ∑ ξ ∈ Ξ, Wint ξ y (bS u) ≠ 0 := by
      intro h0; apply hy; simp only [WaC, h0, mul_zero]
    obtain ⟨ξ, -, hξ⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
    exact hWint0 ξ y (bS u) hξ
  have hTW : ∀ (u : Kˣ) (n₀ : Fin T.card → ℤ) (σ : ℂ), ∃ (G : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
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
        G ((Log u).1 + x, Θ) = (∏ j, tvec j ^ (-(n₀ j + k j))) *
          (σ * WaC u (P (sgn (emb u)) ((Log u).1, arg (emb u)) * P 1 (x, θ))) := by
    intro u n₀ σ
    obtain ⟨G, hG, ⟨Rb, hRb, hsupp⟩, hper, hid⟩ :=
      NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
        K (P (sgn (emb u))) (P 1) (hP_smooth _) (hP_per _) (hP_mul' _) (hP_bdd' _)
        (fun x => σ * WaC u x) (contDiff_const.mul (hWaC_smooth u)) C₀ hC₀ hC₀u
        (fun y hy => hWaC0 u y (fun h => hy (show σ * WaC u y = 0 by rw [h, mul_zero]))) cs ts tvec htvec ℓ
        (Log u).1 (arg (emb u)) n₀
    exact ⟨G, Rb, hG, hRb, hsupp, hper, hid⟩
  choose Gf Rbf hGf_smooth hRbf hGf_supp hGf_per hGf_id using hTW

  let I₀ := ↥hBfin.toFinset × ↥hμfin.toFinset × Fin nC
  let urep : I₀ → Kˣ := fun i => ub i.1 * (i.2.1 : Kˣ) * cC i.2.2
  let n₀f : Kˣ → Fin T.card → ℤ := fun u j => -((Log u).2 j / (f (T.equivFin.symm j).1 : ℤ))
  let N : ℕ := Fintype.card I₀ + 1
  let eI : I₀ ≃ Fin (Fintype.card I₀) := Fintype.equivFin I₀
  let sub : Fin N → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) :=
    Fin.lastCases ⊥ (fun _ => sub₀)
  let G : Fin N → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) ×
      (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ :=
    Fin.lastCases (Gf 1 (n₀f 1) (-1)) (fun i => Gf (urep (eI.symm i)) (n₀f (urep (eI.symm i))) 1)
  let Rb : ℝ := Rbf 1 (n₀f 1) (-1) + ∑ i : I₀, Rbf (urep i) (n₀f (urep i)) 1
  let x₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ :=
    Fin.lastCases (Log 1).1 (fun i => (Log (urep (eI.symm i))).1)
  let n₀ : Fin N → Fin T.card → ℤ := Fin.lastCases (n₀f 1) (fun i => n₀f (urep (eI.symm i)))
  have hRb0 : 0 ≤ Rb := add_nonneg (hRbf _ _ _) (Finset.sum_nonneg fun i _ => hRbf _ _ _)
  have hRb_ge : ∀ i : I₀, Rbf (urep i) (n₀f (urep i)) 1 ≤ Rb := fun i =>
    le_add_of_nonneg_of_le (hRbf _ _ _) (Finset.single_le_sum (fun i _ => hRbf (urep i) (n₀f (urep i)) 1) (Finset.mem_univ i))
  have hRb_geg : Rbf 1 (n₀f 1) (-1) ≤ Rb := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hRbf _ _ _)
  refine ⟨N, Λ, hΛ_disc, sl, ω, hω, hpf, χ, lift, hcompat, sub, ?_, G, ?_, Rb, hRb0, ?_, ?_, x₀, n₀, fun _ => 0,
    fun n => ?_⟩
  · intro i; refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [sub, Fin.lastCases_last]; exact bot_le
    · simp only [sub, Fin.lastCases_castSucc]; exact hsub₀Λ
  · intro i; refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [G, Fin.lastCases_last]; exact hGf_smooth _ _ _
    · simp only [G, Fin.lastCases_castSucc]; exact hGf_smooth _ _ _
  · intro i p hp; revert hp; refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hp; simp only [G, Fin.lastCases_last]
      exact hGf_supp _ _ _ p (hp.imp fun k hk => lt_of_le_of_lt hRb_geg hk)
    · intro hp; simp only [G, Fin.lastCases_castSucc]
      exact hGf_supp _ _ _ p (hp.imp fun k hk => lt_of_le_of_lt (hRb_ge _) hk)
  · intro i p J; refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [G, Fin.lastCases_last]; exact hGf_per _ _ _ p J
    · simp only [G, Fin.lastCases_castSucc]; exact hGf_per _ _ _ p J

  let I' : Set Kˣ := {u | (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (ιK u) = 0) ∧
    ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (ιK u) = (f (T.equivFin.symm i).1 : ℤ) * n i}
  let In : Set Kˣ := {u | (u : K) ≠ 1 ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (ιK u) = 0) ∧
    ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (ιK u) = (f (T.equivFin.symm i).1 : ℤ) * n i}
  change C * ∑ᶠ u ∈ In, term n u = _
  have hord : ∀ (u : Kˣ) (v : HeightOneSpectrum (𝓞 K)),
      NumberField.Idele.ord K v (ιK u) = -Multiplicative.toAdd (v.valuationOfNeZero u) := fun u v => NumCore.ord_unitsMap K u v
  have hIn_eq : In = I' \ {1} := by
    ext u
    simp only [In, I', Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff, ne_eq, Units.val_eq_one]
    tauto
  have hLog_one : Log 1 = 0 := by
    have := hLog_mul 1 1
    rw [mul_one] at this
    have h2 : Log 1 + Log 1 = Log 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h2
  have hLog_inv : ∀ a : Kˣ, Log a⁻¹ = -Log a := fun a => by
    have := hLog_mul a⁻¹ a
    rw [inv_mul_cancel, hLog_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm

  have hI'_val : ∀ u : Kˣ, u ∈ I' ↔ (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero u = 1) ∧
      ∀ i : Fin T.card, (Log u).2 i = -((f (T.equivFin.symm i).1 : ℤ) * n i) := by
    intro u
    simp only [I', Set.mem_setOf_eq, hord, hLog2]
    refine and_congr (forall_congr' fun v => forall_congr' fun _ => forall_congr' fun _ => ?_)
      (forall_congr' fun i => ?_)
    · rw [neg_eq_zero, toAdd_eq_zero]
    · constructor <;> intro h <;> linarith

  obtain ⟨R₀, hR₀⟩ := hP_bdd C₀ hC₀ hC₀u
  have hterm_supp : ∀ u : Kˣ, term n u ≠ 0 →
      (∀ i, |(Log u).1 i| ≤ R₀) ∧ ∀ v : ↥SK, ((u : K) : v.1.adicCompletion K) ∈ Cv v.1 := by
    intro u hu
    have hsum : ∑ ξ ∈ Ξ, Wint ξ (emb u) (bS u) ≠ 0 := by
      intro h0; apply hu; simp only [term, h0, mul_zero]
    obtain ⟨ξ, hξ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    refine ⟨?_, fun v => ?_⟩
    · have hC : emb u ∈ C₀ := hWint0 ξ _ _ hne
      rw [← hP_inv' u] at hC
      exact hR₀ _ _ _ hC
    · by_contra hv
      apply hne
      refine (hCf ⟨ξ, hξ⟩).2 (emb u) (bS u) ⟨v.1, v.2, fun h => hv ?_⟩
      rw [hbS] at h
      exact Set.mem_iUnion.2 ⟨⟨ξ, hξ⟩, h⟩
  have hI'Q : ∀ u ∈ I', term n u ≠ 0 → u ∈ Q := by
    intro u hu hne
    have hu' := (hI'_val u).1 hu
    refine ⟨hu'.1, fun v hv => ?_, (hterm_supp u hne).2⟩
    have := hu'.2 (T.equivFin ⟨v, hv⟩)
    rw [hLog2] at this
    simp only [Equiv.symm_apply_apply] at this
    rw [this]
    exact (dvd_mul_right _ _).neg_right

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
  have hSfin : (I' ∩ Function.support (term n)).Finite := by
    refine (Set.Finite.biUnion (Set.finite_univ : (Set.univ : Set ↥hBfin.toFinset).Finite) fun β _ =>
      ((hboxfin (R₀ + ∑ i, |(Log (ub β)).1 i|) (fun j => -((f (T.equivFin.symm j).1 : ℤ) * n j) - (Log (ub β)).2 j)).image
        fun a => ub β * a)).subset ?_
    rintro u ⟨huI, hu⟩
    have huQ := hI'Q u huI hu
    refine Set.mem_biUnion (Set.mem_univ (⟨pat u, hβ_of u huQ⟩ : ↥hBfin.toFinset)) ⟨(ub ⟨pat u, hβ_of u huQ⟩)⁻¹ * u, ⟨?_, ?_, ?_⟩, by group⟩
    · exact ((hA_mem _).1 (hdivA u huQ)).1
    · intro i
      rw [hLog_mul, hLog_inv, Prod.fst_add, Prod.fst_neg, Pi.add_apply, Pi.neg_apply]
      have h1 := (hterm_supp u hu).1 i
      have h2 : |(Log (ub ⟨pat u, hβ_of u huQ⟩)).1 i| ≤ ∑ i, |(Log (ub ⟨pat u, hβ_of u huQ⟩)).1 i| :=
        Finset.single_le_sum (f := fun i => |(Log (ub ⟨pat u, hβ_of u huQ⟩)).1 i|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      calc |-(Log (ub ⟨pat u, hβ_of u huQ⟩)).1 i + (Log u).1 i|
          ≤ |-(Log (ub ⟨pat u, hβ_of u huQ⟩)).1 i| + |(Log u).1 i| := abs_add_le _ _
        _ ≤ _ := by rw [abs_neg]; linarith
    · funext j
      rw [hLog_mul, hLog_inv, Prod.snd_add, Prod.snd_neg, Pi.add_apply, Pi.neg_apply, ((hI'_val u).1 huI).2 j]
      ring
  have hInfin : (In ∩ Function.support (term n)).Finite :=
    hSfin.subset (Set.inter_subset_inter_left _ (by rw [hIn_eq]; exact Set.diff_subset))

  have hghost_split : ∑ᶠ u ∈ I', term n u = ∑ᶠ u ∈ In, term n u + (if (1 : Kˣ) ∈ I' then term n 1 else 0) := by
    by_cases h1 : (1 : Kˣ) ∈ I'
    · rw [if_pos h1]
      have : I' = insert 1 In := by
        rw [hIn_eq, Set.insert_diff_singleton, Set.insert_eq_of_mem h1]
      rw [this, finsum_mem_insert' _ (by rw [hIn_eq]; simp) hInfin, add_comm]
    · rw [if_neg h1, add_zero, hIn_eq, Set.diff_singleton_eq_self h1]

  have hpat_mulA : ∀ (u a : Kˣ), a ∈ A → pat (u * a) = pat u := by
    intro u a ha
    funext v
    rw [hpat, hpat, map_mul, ((hA_mem a).1 ha).1 v.1 (hST v.1 v.2), mul_one]
  let gβ : ↥hBfin.toFinset → Kˣ → ℂ := fun β a => if ub β * a ∈ I' then term n (ub β * a) else 0
  have hsplit : ∑ᶠ u ∈ I', term n u = ∑ β : ↥hBfin.toFinset, ∑ᶠ a ∈ (A : Set Kˣ), gβ β a := by
    let Sβ : ↥hBfin.toFinset → Set Kˣ := fun β =>
      (I' ∩ (fun a => ub β * a) '' (A : Set Kˣ)) ∩ Function.support (term n)
    have hSβfin : ∀ β, (Sβ β).Finite := fun β =>
      hSfin.subset (Set.inter_subset_inter_left _ Set.inter_subset_left)
    have hSβdisj : Pairwise (fun β β' => Disjoint (Sβ β) (Sβ β')) := by
      intro β β' hne
      refine Set.disjoint_left.2 fun u hu hu' => hne ?_
      obtain ⟨a, ha, hua⟩ := hu.1.2
      obtain ⟨a', ha', hua'⟩ := hu'.1.2
      have hua₁ : ub β * a = u := hua
      have hua₂ : ub β' * a' = u := hua'
      apply Subtype.ext
      rw [← hubpat β, ← hubpat β', ← hpat_mulA (ub β) a ha, ← hpat_mulA (ub β') a' ha', hua₁, hua₂]
    have hUn : I' ∩ Function.support (term n) = ⋃ β, Sβ β := by
      ext u
      constructor
      · rintro ⟨huI, hu⟩
        have huQ := hI'Q u huI hu
        exact Set.mem_iUnion.2 ⟨⟨pat u, hβ_of u huQ⟩,
          ⟨huI, (ub ⟨pat u, hβ_of u huQ⟩)⁻¹ * u, hdivA u huQ, mul_inv_cancel_left _ _⟩, hu⟩
      · intro h
        obtain ⟨β, hβ⟩ := Set.mem_iUnion.1 h
        exact ⟨hβ.1.1, hβ.2⟩
    calc ∑ᶠ u ∈ I', term n u = ∑ᶠ u ∈ I' ∩ Function.support (term n), term n u :=
          (finsum_mem_inter_support _ _).symm
      _ = ∑ᶠ u ∈ ⋃ β, Sβ β, term n u := by rw [hUn]
      _ = ∑ᶠ β, ∑ᶠ u ∈ Sβ β, term n u := finsum_mem_iUnion hSβdisj hSβfin
      _ = ∑ β, ∑ᶠ u ∈ Sβ β, term n u := finsum_eq_sum_of_fintype _
      _ = ∑ β, ∑ᶠ a ∈ (A : Set Kˣ), gβ β a := Finset.sum_congr rfl fun β _ => ?_
    have hbij : Set.BijOn (fun a => ub β * a) ((A : Set Kˣ) ∩ {a | ub β * a ∈ I'})
        (I' ∩ (fun a => ub β * a) '' (A : Set Kˣ)) := by
      refine ⟨fun a ha => ⟨ha.2, a, ha.1, rfl⟩, (mul_right_injective (ub β)).injOn, ?_⟩
      rintro u ⟨huI, a, ha, rfl⟩
      exact ⟨a, ⟨ha, huI⟩, rfl⟩
    calc ∑ᶠ u ∈ Sβ β, term n u = ∑ᶠ u ∈ I' ∩ (fun a => ub β * a) '' (A : Set Kˣ), term n u :=
          finsum_mem_inter_support _ _
      _ = ∑ᶠ a ∈ (A : Set Kˣ) ∩ {a | ub β * a ∈ I'}, term n (ub β * a) :=
          (finsum_mem_eq_of_bijOn _ hbij (fun a _ => rfl)).symm
      _ = ∑ᶠ a ∈ (A : Set Kˣ), gβ β a := (NumCore.finsum_mem_ite _ _ _).symm

  have hICβ : ∀ β : ↥hBfin.toFinset, ∑ᶠ a ∈ (A : Set Kˣ), gβ β a =
      ∑ z ∈ hμfin.toFinset, ∑ j : Fin nC, ∑ᶠ h ∈ (H : Set Kˣ), gβ β (z * cC j * h) := by
    intro β
    refine hIC2ℂ (gβ β) ?_
    refine ((hSfin.preimage ((mul_right_injective (ub β)).injOn)).subset ?_)
    rintro a ⟨-, hga⟩
    rw [Function.mem_support] at hga
    by_cases h : ub β * a ∈ I'
    · refine ⟨h, ?_⟩
      rw [Function.mem_support]
      simpa [gβ, h] using hga
    · exact absurd (by simp [gβ, h]) hga

  have hE1 : ∀ (u : Kˣ), (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero u = 1) →
      (∀ j : Fin T.card, (f (T.equivFin.symm j).1 : ℤ) ∣ (Log u).2 j) →
      ∀ (σ : ℂ), ∀ h ∈ H,
        σ * (C * (if u * h ∈ I' then term n (u * h) else 0)) =
          (if (Lmap h).2 + n₀f u = n then Gf u (n₀f u) σ ((Log u).1 + (Lmap h).1, 0 + lift (Lmap h)) else 0) := by
    intro u huT hudvd σ h hh
    have hhF := hHF hh
    have hhA := hHA hh
    have hhFA := hHFA hh
    obtain ⟨-, -, hhU, hhpos⟩ := (hH_mem h).1 hh
    have hcond : (u * h ∈ I') ↔ (Lmap h).2 + n₀f u = n := by
      rw [hI'_val]
      constructor
      · rintro ⟨-, h2⟩
        funext j
        have hj := h2 j
        rw [hLog_mul, Prod.snd_add, Pi.add_apply] at hj
        show -((Log h).2 j / (f (T.equivFin.symm j).1 : ℤ)) + -((Log u).2 j / (f (T.equivFin.symm j).1 : ℤ)) = n j
        apply mul_left_cancel₀ (hf0 j)
        rw [mul_add, mul_neg, mul_neg, Int.mul_ediv_cancel' (hfdvd h hhA j), Int.mul_ediv_cancel' (hudvd j)]
        linarith
      · intro hn
        refine ⟨fun v hvS hvT => by rw [map_mul, huT v hvS hvT, ((hA_mem h).1 hhA).1 v hvT, mul_one], fun j => ?_⟩
        have hj := congr_fun hn j
        simp only [Pi.add_apply] at hj
        rw [hLog_mul, Prod.snd_add, Pi.add_apply]
        have e1 := Int.mul_ediv_cancel' (hfdvd h hhA j)
        have e2 := Int.mul_ediv_cancel' (hudvd j)
        rw [← hj, mul_add, mul_neg, mul_neg, e1, e2]
        ring
    by_cases hc : (Lmap h).2 + n₀f u = n
    · rw [if_pos (hcond.2 hc), if_pos hc]

      have hW : ∀ ξ (x : mixedEmbedding.mixedSpace K), Wint ξ x (bS (u * h)) = Wint ξ x (bS u) := by
        intro ξ x
        have hprod : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
            (∏ v ∈ SK, Φf v (bS (u * h) v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) =
            ∏ v ∈ SK, Φf v (bS u v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) := by
          intro zS
          refine Finset.prod_congr rfl fun v hv => ?_
          have e : bS (u * h) v = bS u v * bS h v := by
            simp only [bS, map_mul, Units.val_mul]
            rfl
          have := (hU v hv).2 _ (hhU v hv) (bS u v)
            ((((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
          rw [Units.coe_map, MonoidHom.coe_coe, NumCore.algebraMap_adicCompletion_apply] at this
          rw [e, hbS h]
          exact this
        simp only [Wint, hprod]

      have hembuh : emb (u * h) = P (sgn (emb u)) ((Log u).1, arg (emb u)) * P 1 ((Log h).1, arg (emb h)) := by
        rw [hemb_mul, hP_inv' u]
        congr 1
        have h1 : sgn (emb h) = 1 := hsgn1 (emb h) (hemb_unit h) (fun w => by rw [hemb]; exact hhpos w)
        conv_lhs => rw [← hP_inv' h, h1]

      have hk : ∀ j : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm j).1 (ιK h) =
          (f (T.equivFin.symm j).1 : ℤ) * (Lmap h).2 j := by
        intro j
        rw [hord, ← hLog2]
        show -(Log h).2 j = (f (T.equivFin.symm j).1 : ℤ) * -((Log h).2 j / (f (T.equivFin.symm j).1 : ℤ))
        rw [mul_neg, Int.mul_ediv_cancel' (hfdvd h hhA j)]
      have hℓ' : Real.exp (ℓ (Lmap h).1) = ∏ j, ‖tvec j‖ ^ (-((Lmap h).2 j)) := by
        have := hℓ h (hF_T h hhF) (fun j => (Lmap h).2 j) hk
        have hX : (fun i => (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) (h : K))) = (Lmap h).1 := by
          show _ = (Log h).1
          rw [hLog]
        rw [hX] at this
        exact this
      have hcs' : ∀ j, (((0 + lift (Lmap h)) (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((arg (emb h) j : ℝ) : AddCircle (1 : ℝ)) := by
        intro j
        rw [zero_add, hemb]
        have := (hliftF h hhFA).1 ((Fintype.equivFin {w : NumberField.InfinitePlace K // w.IsComplex}).symm j)
        simp only [Equiv.apply_symm_apply] at this
        exact this
      have hts' : ∀ j, (((0 + lift (Lmap h)) (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-((Lmap h).2 j : ℝ) * (tvec j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) := by
        intro j
        rw [zero_add, (hliftF h hhFA).2 j]
        congr 1
        simp only [bvec]
        ring
      have hid := hGf_id u (n₀f u) σ (Lmap h).1 (arg (emb h)) (fun j => (Lmap h).2 j) (0 + lift (Lmap h)) hcs' hts' hℓ'
      rw [hid]
      have hn : ∀ j, n j = n₀f u j + (Lmap h).2 j := fun j => by
        rw [← hc]; simp only [Pi.add_apply]; ring
      have htilt : tilt n = ∏ j, tvec j ^ (-(n₀f u j + (Lmap h).2 j)) := by
        simp only [tilt]
        exact Finset.prod_congr rfl fun j _ => by rw [hn j]
      simp only [term, hW, htilt, WaC]
      rw [hembuh]
      conv_lhs => rw [mul_left_comm C, mul_left_comm σ]
    · rw [if_neg (mt hcond.1 hc), if_neg hc, mul_zero, mul_zero]

  have hE2 : ∀ (u : Kˣ) (σ : ℂ),
      ∑ᶠ h ∈ (H : Set Kˣ), (if (Lmap h).2 + n₀f u = n then Gf u (n₀f u) σ ((Log u).1 + (Lmap h).1, 0 + lift (Lmap h)) else 0) =
      ∑' γ : sub₀, (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀f u = n then
        Gf u (n₀f u) σ ((Log u).1 + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1,
          0 + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0) := by
    intro u σ
    let Ψ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → ℂ := fun γ =>
      if γ.2 + n₀f u = n then Gf u (n₀f u) σ ((Log u).1 + γ.1, 0 + lift γ) else 0
    show ∑ᶠ h ∈ (H : Set Kˣ), Ψ (Lmap h) = ∑' γ : sub₀, Ψ γ
    have hinj : Set.InjOn Lmap (H : Set Kˣ) := by
      intro a ha b hb hab
      have h0 : Lmap (a * b⁻¹) = 0 := by
        rw [hL_add a (hHFA ha) b⁻¹ (FA.inv_mem (hHFA hb)), hL_inv b (hHFA hb), hab, add_neg_cancel]
      have := hL_inj _ (FA.mul_mem (hHFA ha) (FA.inv_mem (hHFA hb))) h0
      rw [mul_inv_eq_one] at this
      exact this
    have hbij : Set.BijOn Lmap (H : Set Kˣ) (sub₀ : Set _) := by
      refine ⟨fun h hh => ?_, hinj, fun γ hγ => ?_⟩
      · rw [SetLike.mem_coe, hsub₀_mem]
        exact ⟨h, hh, rfl⟩
      · rw [SetLike.mem_coe, hsub₀_mem] at hγ
        obtain ⟨h, hh, hγ⟩ := hγ
        exact ⟨h, hh, hγ⟩
    have h1 : ∑ᶠ h ∈ (H : Set Kˣ), Ψ (Lmap h) = ∑ᶠ γ ∈ (sub₀ : Set _), Ψ γ :=
      finsum_mem_eq_of_bijOn _ hbij (fun _ _ => rfl)
    have hfinΨ : (Function.support fun γ : ↥sub₀ => Ψ γ).Finite := by
      haveI := hΛ_disc
      have hF := AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology Λ
        (Rbf u (n₀f u) σ + ∑ i, |(Log u).1 i|) (n - n₀f u)
      refine (hF.preimage (Subtype.val_injective.injOn)).subset ?_
      intro γ hγ
      rw [Function.mem_support] at hγ
      by_cases hc : (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀f u = n
      · refine ⟨hsub₀Λ γ.2, fun i => ?_, by rw [← hc]; simp⟩
        by_contra hlt
        push_neg at hlt
        apply hγ
        show Ψ γ = 0
        simp only [Ψ, if_pos hc]
        apply hGf_supp u (n₀f u) σ
        refine ⟨i, ?_⟩
        simp only [Pi.add_apply]
        have h2 : |(Log u).1 i| ≤ ∑ i, |(Log u).1 i| :=
          Finset.single_le_sum (f := fun i => |(Log u).1 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
        have h3 : |(γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1 i| ≤
            |(Log u).1 i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1 i| + |(Log u).1 i| := by
          have := abs_sub ((Log u).1 i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1 i) ((Log u).1 i)
          simp only [add_sub_cancel_left] at this
          linarith
        linarith
      · exact absurd (show Ψ γ = 0 by simp only [Ψ, if_neg hc]) hγ
    rw [h1, ← finsum_set_coe_eq_finsum_mem, tsum_eq_finsum hfinΨ]
    rfl

  have hghost : (-1 : ℂ) * (C * (if (1 : Kˣ) ∈ I' then term n 1 else 0)) =
      ∑' γ : (⊥ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))),
        (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀f 1 = n then
          Gf 1 (n₀f 1) (-1) ((Log 1).1 + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1,
            0 + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0) := by
    have h := hE1 1 (fun v _ _ => by rw [map_one]) (fun j => by rw [hLog_one]; exact dvd_zero _) (-1) 1 H.one_mem
    rw [mul_one] at h
    rw [h, hL_one]
    rw [tsum_eq_single (⟨0, (⊥ : AddSubgroup _).zero_mem⟩ : ↥(⊥ : AddSubgroup
      ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))))
      (fun b' hb' => absurd (Subsingleton.elim b' _) hb')]

  have hsubl : sub (Fin.last (Fintype.card I₀)) = ⊥ := by simp only [sub, Fin.lastCases_last]
  have hsubc : ∀ i : Fin (Fintype.card I₀), sub (Fin.castSucc i) = sub₀ := fun i => by
    simp only [sub, Fin.lastCases_castSucc]
  have hGl : G (Fin.last (Fintype.card I₀)) = Gf 1 (n₀f 1) (-1) := by simp only [G, Fin.lastCases_last]
  have hGc : ∀ i : Fin (Fintype.card I₀), G (Fin.castSucc i) = Gf (urep (eI.symm i)) (n₀f (urep (eI.symm i))) 1 :=
    fun i => by simp only [G, Fin.lastCases_castSucc]
  have hx₀l : x₀ (Fin.last (Fintype.card I₀)) = (Log 1).1 := by simp only [x₀, Fin.lastCases_last]
  have hx₀c : ∀ i : Fin (Fintype.card I₀), x₀ (Fin.castSucc i) = (Log (urep (eI.symm i))).1 :=
    fun i => by simp only [x₀, Fin.lastCases_castSucc]
  have hn₀l : n₀ (Fin.last (Fintype.card I₀)) = n₀f 1 := by simp only [n₀, Fin.lastCases_last]
  have hn₀c : ∀ i : Fin (Fintype.card I₀), n₀ (Fin.castSucc i) = n₀f (urep (eI.symm i)) :=
    fun i => by simp only [n₀, Fin.lastCases_castSucc]
  rw [Fin.sum_univ_castSucc, hsubl, hGl, hx₀l, hn₀l]
  rw [show C * ∑ᶠ u ∈ In, term n u = C * ∑ᶠ u ∈ I', term n u + (-1) * (C * (if (1 : Kˣ) ∈ I' then term n 1 else 0)) by
    rw [hghost_split]; ring]
  rw [hghost, hsplit, Finset.mul_sum]
  congr 1
  symm
  refine (Fintype.sum_equiv eI.symm _ (fun p : I₀ => ∑' γ : sub₀,
    (if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀f (urep p) = n then
      Gf (urep p) (n₀f (urep p)) 1 ((Log (urep p)).1 + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1,
        0 + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))) else 0)) (fun i => ?_)).trans ?_
  · rw [hsubc i, hGc i, hx₀c i, hn₀c i]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Fintype.sum_prod_type, hICβ β, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hz : (z : Kˣ) ∈ A := hμA ((hμfin.mem_toFinset).1 z.2)
  have hu_T : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → v.valuationOfNeZero (ub β * (z : Kˣ) * cC j) = 1 := by
    intro v hvS hvT
    rw [map_mul, map_mul, (hubQ β).1 v hvS hvT, ((hA_mem _).1 hz).1 v hvT, ((hA_mem _).1 (hcA j)).1 v hvT, one_mul, one_mul]
  have hu_dvd : ∀ j' : Fin T.card, (f (T.equivFin.symm j').1 : ℤ) ∣ (Log (ub β * (z : Kˣ) * cC j)).2 j' := by
    intro j'
    rw [hLog_mul, hLog_mul, Prod.snd_add, Prod.snd_add, Pi.add_apply, Pi.add_apply]
    refine dvd_add (dvd_add ?_ (hfdvd _ hz j')) (hfdvd _ (hcA j) j')
    rw [hLog2]
    exact (hubQ β).2.1 _ (T.equivFin.symm j').2
  symm
  rw [mul_finsum_mem, ← hE2 (ub β * (z : Kˣ) * cC j) 1]
  refine finsum_mem_congr rfl fun h hh => ?_
  have := hE1 (ub β * (z : Kˣ) * cC j) hu_T hu_dvd 1 h hh
  rw [one_mul] at this
  rw [← this]
  simp only [gβ, mul_assoc]

end S_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
end P2MW
export P2MW.S_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant (solution)
