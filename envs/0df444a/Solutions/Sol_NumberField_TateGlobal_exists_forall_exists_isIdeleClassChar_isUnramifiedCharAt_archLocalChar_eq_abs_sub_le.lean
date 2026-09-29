-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1ea86b57-66d8-5559-966e-83ee343194a9

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace R4TwistNormExist

section Extension

noncomputable scoped instance instDivisibleByAdditiveCircle : DivisibleBy (Additive Circle) ℤ where
  div a n := Additive.ofMul (Circle.exp (Complex.arg ((a.toMul : Circle) : ℂ) / n))
  div_zero a := by
    simp only [Int.cast_zero, div_zero]
    rw [show Circle.exp 0 = 1 from Circle.exp_zero]; rfl
  div_cancel {n} a hn := by
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    apply Subtype.ext
    rw [Circle.coe_zpow, Circle.coe_exp, ← Complex.exp_int_mul, Complex.ofReal_div, Complex.ofReal_intCast,
      ← mul_assoc, mul_div_cancel₀ _ (by exact_mod_cast hn), ← Circle.coe_exp, Circle.exp_arg]

theorem exists_monoidHom_extend {G : Type*} [CommGroup G] (S : Subgroup G) (f : S →* Circle) :
    ∃ h : G →* Circle, ∀ s : S, h s = f s := by
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive S.subtype) (fun a b hab => by
      have : (a.toMul : G) = (b.toMul : G) := by
        simpa [MonoidHom.toAdditive] using hab
      exact Additive.toMul.injective (Subtype.ext this)) (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm h, fun s => ?_⟩
  have := congrArg (fun φ : Additive S →+ Additive Circle => (φ (Additive.ofMul s)).toMul) hh
  simpa [MonoidHom.toAdditive] using this

theorem exists_monoidHom_extend_trivial {G : Type*} [CommGroup G] (P U : Subgroup G) (f : U →* Circle)
    (hf : ∀ u : U, (u : G) ∈ P → f u = 1) :
    ∃ η : G →* Circle, (∀ p : G, p ∈ P → η p = 1) ∧ ∀ u : U, η u = f u := by
  set π : G →* G ⧸ P := QuotientGroup.mk' P with hπ
  set φ : U →* U.map π := π.subgroupMap U with hφ
  have hφs : Function.Surjective φ := π.subgroupMap_surjective U
  have hker : φ.ker ≤ f.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h1 : (π u : G ⧸ P) = 1 := by
      have := congrArg (fun x : U.map π => (x : G ⧸ P)) hu
      simpa [hφ] using this
    exact hf u ((QuotientGroup.eq_one_iff (u : G)).mp h1)
  set fbar : U.map π →* Circle := MonoidHom.liftOfSurjective φ hφs ⟨f, hker⟩ with hfbar
  obtain ⟨h, hh⟩ := exists_monoidHom_extend (U.map π) fbar
  refine ⟨h.comp π, fun p hp => ?_, fun u => ?_⟩
  · rw [MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff p).mpr hp, map_one]
  · have e1 : π u = ((φ u : U.map π) : G ⧸ P) := rfl
    rw [MonoidHom.comp_apply, e1, hh (φ u), hfbar, MonoidHom.liftOfRightInverse_comp_apply]

end Extension

section Arch

variable (F : Type) [Field F] [NumberField F]

noncomputable def evalC (w : InfinitePlace F) : mixedSpace F →+* ℂ :=
  if hw : IsReal w then
    Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ : {w : InfinitePlace F // IsReal w} => ℝ) ⟨w, hw⟩).comp
      (RingHom.fst _ _))
  else
    (Pi.evalRingHom (fun _ : {w : InfinitePlace F // IsComplex w} => ℂ) ⟨w, not_isReal_iff_isComplex.mp hw⟩).comp
      (RingHom.snd _ _)

variable {F}

theorem evalC_apply_of_isReal {w : InfinitePlace F} (hw : IsReal w) (x : mixedSpace F) :
    evalC F w x = ((x.1 ⟨w, hw⟩ : ℝ) : ℂ) := by
  rw [evalC, dif_pos hw]; rfl

theorem evalC_apply_of_isComplex {w : InfinitePlace F} (hw : IsComplex w) (x : mixedSpace F) :
    evalC F w x = x.2 ⟨w, hw⟩ := by
  rw [evalC, dif_neg (not_isReal_iff_isComplex.mpr hw)]; rfl

theorem norm_evalC (w : InfinitePlace F) (x : mixedSpace F) : ‖evalC F w x‖ = normAtPlace w x := by
  by_cases hw : IsReal w
  · rw [evalC_apply_of_isReal hw, normAtPlace_apply_of_isReal hw, Complex.norm_real]
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    rw [evalC_apply_of_isComplex hc, normAtPlace_apply_of_isComplex hc]

theorem evalC_mixedEmbedding (w : InfinitePlace F) (k : F) :
    evalC F w (mixedEmbedding F k) = w.embedding k := by
  by_cases hw : IsReal w
  · rw [evalC_apply_of_isReal hw, mixedEmbedding_apply_isReal, embedding_of_isReal_apply]
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    rw [evalC_apply_of_isComplex hc, mixedEmbedding_apply_isComplex]

theorem evalC_ringEquiv_mixedSpace (w : InfinitePlace F) (y : InfiniteAdeleRing F) :
    evalC F w (InfiniteAdeleRing.ringEquiv_mixedSpace F y) = Completion.extensionEmbedding w (y w) := by
  by_cases hw : IsReal w
  · rw [evalC_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact Completion.extensionEmbeddingOfIsReal_apply hw (y w)
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    rw [evalC_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

theorem continuous_evalC (w : InfinitePlace F) : Continuous (evalC F w) := by
  by_cases hw : IsReal w
  · have e : (evalC F w : mixedSpace F → ℂ) = fun x => ((x.1 ⟨w, hw⟩ : ℝ) : ℂ) :=
      funext fun x => evalC_apply_of_isReal hw x
    rw [e]
    exact Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    have e : (evalC F w : mixedSpace F → ℂ) = fun x => x.2 ⟨w, hc⟩ :=
      funext fun x => evalC_apply_of_isComplex hc x
    rw [e]
    exact (continuous_apply _).comp continuous_snd

theorem evalC_ne_zero {w : InfinitePlace F} {x : mixedSpace F} (hx : IsUnit x) : evalC F w x ≠ 0 :=
  (hx.map (evalC F w)).ne_zero

theorem norm_evalC_ne_zero {w : InfinitePlace F} {x : mixedSpace F} (hx : IsUnit x) : ‖evalC F w x‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (evalC_ne_zero hx)

theorem norm_evalC_pos {w : InfinitePlace F} {x : mixedSpace F} (hx : IsUnit x) : 0 < ‖evalC F w x‖ :=
  norm_pos_iff.mpr (evalC_ne_zero hx)

variable (F) in

noncomputable def logAll (x : mixedSpace F) : InfinitePlace F → ℝ :=
  fun w => (mult w : ℝ) * Real.log ‖evalC F w x‖

theorem logAll_mul {x y : mixedSpace F} (hx : IsUnit x) (hy : IsUnit y) : logAll F (x * y) = logAll F x + logAll F y := by
  funext w
  simp only [logAll, Pi.add_apply, map_mul, norm_mul]
  rw [Real.log_mul (norm_evalC_ne_zero hx) (norm_evalC_ne_zero hy), mul_add]

theorem logAll_one : logAll F 1 = 0 := by
  funext w; simp [logAll]

theorem logAll_mixedEmbedding (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    logAll F (mixedEmbedding F ((u : 𝓞 F) : F)) w = (mult w : ℝ) * Real.log (w ((u : 𝓞 F) : F)) := by
  rw [logAll, evalC_mixedEmbedding, norm_embedding_eq]

theorem continuousOn_logAll : ContinuousOn (logAll F) {x : mixedSpace F | IsUnit x} := by
  refine continuousOn_pi.mpr fun w => ?_
  refine ContinuousOn.mul continuousOn_const ?_
  refine ContinuousOn.log ((continuous_evalC w).norm.continuousOn) fun x hx => norm_evalC_ne_zero hx

variable (F) in

noncomputable def sgnC (w : InfinitePlace F) (x : mixedSpace F) : ℂ :=
  evalC F w x * ((‖evalC F w x‖ : ℂ))⁻¹

theorem sgnC_mul (w : InfinitePlace F) {x y : mixedSpace F} :
    sgnC F w (x * y) = sgnC F w x * sgnC F w y := by
  simp only [sgnC, map_mul, norm_mul, Complex.ofReal_mul, mul_inv]
  ring

theorem sgnC_one (w : InfinitePlace F) : sgnC F w 1 = 1 := by
  simp [sgnC]

theorem norm_sgnC (w : InfinitePlace F) {x : mixedSpace F} (hx : IsUnit x) : ‖sgnC F w x‖ = 1 := by
  rw [sgnC, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    mul_inv_cancel₀ (norm_evalC_ne_zero hx)]

theorem sgnC_ne_zero (w : InfinitePlace F) {x : mixedSpace F} (hx : IsUnit x) : sgnC F w x ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_sgnC w hx]; exact one_ne_zero)

theorem sgnC_mixedEmbedding (w : InfinitePlace F) (k : F) :
    sgnC F w (mixedEmbedding F k) = w.embedding k * ((w k : ℝ) : ℂ)⁻¹ := by
  rw [sgnC, evalC_mixedEmbedding, norm_embedding_eq]

theorem continuousOn_sgnC (w : InfinitePlace F) : ContinuousOn (sgnC F w) {x : mixedSpace F | IsUnit x} := by
  have h1 : ContinuousOn (fun y : mixedSpace F => ((‖evalC F w y‖ : ℝ) : ℂ)) {x | IsUnit x} :=
    (Complex.continuous_ofReal.comp (continuous_evalC w).norm).continuousOn
  exact (continuous_evalC w).continuousOn.mul (h1.inv₀ fun x hx => by
    exact_mod_cast norm_evalC_ne_zero hx)

variable (F) in

noncomputable def phase (τ : InfinitePlace F → ℝ) (x : mixedSpace F) : ℝ :=
  ∑ w : InfinitePlace F, τ w * logAll F x w

theorem phase_mul (τ : InfinitePlace F → ℝ) {x y : mixedSpace F} (hx : IsUnit x) (hy : IsUnit y) :
    phase F τ (x * y) = phase F τ x + phase F τ y := by
  simp only [phase, logAll_mul hx hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem phase_one (τ : InfinitePlace F → ℝ) : phase F τ 1 = 0 := by
  simp [phase, logAll_one]

theorem phase_add (τ τ' : InfinitePlace F → ℝ) (x : mixedSpace F) :
    phase F (τ + τ') x = phase F τ x + phase F τ' x := by
  simp only [phase, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem continuousOn_phase (τ : InfinitePlace F → ℝ) : ContinuousOn (phase F τ) {x : mixedSpace F | IsUnit x} := by
  refine continuousOn_finsetSum _ fun w _ => ?_
  exact continuousOn_const.mul ((continuous_apply w).comp_continuousOn continuousOn_logAll)

variable (F) in

noncomputable def archV (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) (x : mixedSpace F) : ℂ :=
  (∏ w : InfinitePlace F, sgnC F w x ^ (m w)) * Complex.exp ((phase F τ x : ℂ) * Complex.I)

variable {τ : InfinitePlace F → ℝ} {m : InfinitePlace F → ℤ}

theorem archV_mul {x y : mixedSpace F} (hx : IsUnit x) (hy : IsUnit y) :
    archV F τ m (x * y) = archV F τ m x * archV F τ m y := by
  simp only [archV, sgnC_mul, mul_zpow, Finset.prod_mul_distrib, phase_mul τ hx hy, Complex.ofReal_add, add_mul,
    Complex.exp_add]
  ring

theorem archV_one : archV F τ m 1 = 1 := by
  simp [archV, sgnC_one, phase_one]

theorem norm_archV {x : mixedSpace F} (hx : IsUnit x) : ‖archV F τ m x‖ = 1 := by
  rw [archV, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_prod]
  exact Finset.prod_eq_one fun w _ => by rw [norm_zpow, norm_sgnC w hx, one_zpow]

theorem archV_ne_zero {x : mixedSpace F} (hx : IsUnit x) : archV F τ m x ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_archV hx]; exact one_ne_zero)

theorem continuousOn_archV : ContinuousOn (archV F τ m) {x : mixedSpace F | IsUnit x} := by
  have h1 : ContinuousOn (fun x : mixedSpace F => ∏ w : InfinitePlace F, sgnC F w x ^ (m w)) {x | IsUnit x} :=
    continuousOn_finsetProd _ fun w _ => (continuousOn_sgnC w).zpow₀ (m w) fun x hx => Or.inl (sgnC_ne_zero w hx)
  have h2 : ContinuousOn (fun x : mixedSpace F => Complex.exp ((phase F τ x : ℂ) * Complex.I)) {x | IsUnit x} :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_phase τ)).mul continuousOn_const)
  exact h1.mul h2

variable (F τ m) in

noncomputable def archHomV : (mixedSpace F)ˣ →* ℂˣ where
  toFun x := Units.mk0 (archV F τ m (x : mixedSpace F)) (archV_ne_zero x.isUnit)
  map_one' := Units.ext (by simp [archV_one])
  map_mul' x y := Units.ext (by simp [archV_mul x.isUnit y.isUnit])

theorem archHomV_apply (x : (mixedSpace F)ˣ) : ((archHomV F τ m x : ℂˣ) : ℂ) = archV F τ m (x : mixedSpace F) := rfl

end Arch

section Global

variable (F : Type) [Field F] [NumberField F]

open IsDedekindDomain.FiniteAdeleRing

theorem isOpen_unitIdeles :
    IsOpen ((unitIdeles (𝓞 F) F : Subgroup (FiniteAdeleRing (𝓞 F) F)ˣ) : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
  have h1 : IsOpen ((fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) ⁻¹'
      AdelicLevel.integralFiniteAdeles (𝓞 F) F) := (isOpen_integralFiniteAdeles (𝓞 F) F).preimage Units.continuous_val
  have h2 : IsOpen ((fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) ⁻¹'
      AdelicLevel.integralFiniteAdeles (𝓞 F) F) := (isOpen_integralFiniteAdeles (𝓞 F) F).preimage Units.continuous_coe_inv
  have e : ((unitIdeles (𝓞 F) F : Subgroup (FiniteAdeleRing (𝓞 F) F)ˣ) : Set (FiniteAdeleRing (𝓞 F) F)ˣ) =
      ((fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 F) F) ∩
      ((fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) ⁻¹'
        AdelicLevel.integralFiniteAdeles (𝓞 F) F) := Set.ext fun _ => Iff.rfl
  rw [e]
  exact h1.inter h2

noncomputable def finPart : (AdeleRing (𝓞 F) F)ˣ →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (adeleFin (𝓞 F) F : AdeleRing (𝓞 F) F →* FiniteAdeleRing (𝓞 F) F)

noncomputable def archMixed : (AdeleRing (𝓞 F) F)ˣ →* (mixedSpace F)ˣ :=
  Units.map (((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (adeleArch (𝓞 F) F) :
    AdeleRing (𝓞 F) F →+* mixedSpace F) : AdeleRing (𝓞 F) F →* mixedSpace F)

noncomputable abbrev unitPartIdeles : Subgroup (AdeleRing (𝓞 F) F)ˣ := (unitIdeles (𝓞 F) F).comap (finPart F)

noncomputable def prin : Fˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)

noncomputable def unitsF : (𝓞 F)ˣ →* Fˣ := Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F)

variable {F}

theorem finPart_apply_val (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((finPart F x : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = (x : AdeleRing (𝓞 F) F).2 := rfl

theorem archMixed_apply_val (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((archMixed F x : (mixedSpace F)ˣ) : mixedSpace F) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (adeleArch (𝓞 F) F (x : AdeleRing (𝓞 F) F)) := rfl

theorem evalC_archMixed (w : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ) :
    evalC F w ((archMixed F x : (mixedSpace F)ˣ) : mixedSpace F) =
      Completion.extensionEmbedding w ((x : AdeleRing (𝓞 F) F).1 w) := by
  rw [archMixed_apply_val, evalC_ringEquiv_mixedSpace]; rfl

theorem mem_unitPartIdeles_iff (x : (AdeleRing (𝓞 F) F)ˣ) : x ∈ unitPartIdeles F ↔ finPart F x ∈ unitIdeles (𝓞 F) F :=
  Iff.rfl

theorem unitsF_val (u : (𝓞 F)ˣ) : ((unitsF F u : Fˣ) : F) = ((u : 𝓞 F) : F) := rfl

theorem archMixed_prin (k : Fˣ) :
    ((archMixed F (prin F k) : (mixedSpace F)ˣ) : mixedSpace F) = mixedEmbedding F (k : F) := by
  rw [archMixed_apply_val, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

theorem finPart_prin_mem (u : (𝓞 F)ˣ) : finPart F (prin F (unitsF F u)) ∈ unitIdeles (𝓞 F) F := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (u : 𝓞 F)
  · rw [← map_inv, ← map_inv, ← map_inv]
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)

theorem prin_unitsF_mem (u : (𝓞 F)ˣ) : prin F (unitsF F u) ∈ unitPartIdeles F := finPart_prin_mem u

variable (F) in

noncomputable def unitsIdele : (𝓞 F)ˣ →* ↥(unitPartIdeles F) :=
  ((prin F).comp (unitsF F)).codRestrict (unitPartIdeles F) prin_unitsF_mem

theorem exists_unitsF_eq_of_mem {k : Fˣ} (hk : prin F k ∈ unitPartIdeles F) : ∃ u : (𝓞 F)ˣ, unitsF F u = k := by
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (k : F) ≤ 1 := fun v => by
    have h : ((k : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hk.1 v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  have hint' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((k⁻¹ : Fˣ) : F) ≤ 1 := fun v => by
    have h : (((k⁻¹ : Fˣ) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hk.2 v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (k : F) hint
  obtain ⟨r', hr'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((k⁻¹ : Fˣ) : F) hint'
  have hrr' : r * r' = 1 := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, hr, hr', map_one, Units.mul_inv]
  refine ⟨⟨r, r', hrr', by rw [mul_comm]; exact hrr'⟩, Units.ext ?_⟩
  rw [unitsF_val]; exact hr

variable (F) in

noncomputable def partialChar (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) :
    ↥(unitPartIdeles F) →* ℂˣ :=
  (archHomV F τ m).comp ((archMixed F).comp (unitPartIdeles F).subtype)

theorem partialChar_apply_val (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) (x : ↥(unitPartIdeles F)) :
    ((partialChar F τ m x : ℂˣ) : ℂ) = archV F τ m ((archMixed F (x : (AdeleRing (𝓞 F) F)ˣ) : (mixedSpace F)ˣ) : mixedSpace F) :=
  rfl

theorem partialChar_unitsIdele_val (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) (u : (𝓞 F)ˣ) :
    ((partialChar F τ m (unitsIdele F u) : ℂˣ) : ℂ) = archV F τ m (mixedEmbedding F ((u : 𝓞 F) : F)) := by
  rw [partialChar_apply_val]
  have e2 : ((archMixed F ((unitsIdele F u : ↥(unitPartIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) : (mixedSpace F)ˣ) :
      mixedSpace F) = mixedEmbedding F ((u : 𝓞 F) : F) := archMixed_prin (unitsF F u)
  rw [e2]

end Global

section Interpolation

variable (F : Type) [Field F] [NumberField F]

noncomputable def logBasis : Module.Basis (Fin (rank F)) ℝ (logSpace F) :=
  Module.Basis.ofZLatticeBasis ℝ (unitLattice F) (basisUnitLattice F)

noncomputable def basisConst : ℝ :=
  Real.pi * ∑ w : {w : InfinitePlace F // w ≠ w₀}, ∑ i : Fin (rank F), |(logBasis F).repr (Pi.single w 1) i|

noncomputable def bound : ℝ := 2 * basisConst F + (torsionOrder F : ℝ)

noncomputable def weightOf (b : InfinitePlace F → ℤ) : InfinitePlace F → ℤ :=
  fun w => if IsReal w then 0 else (torsionOrder F : ℤ) * (b w / (torsionOrder F : ℤ))

variable {F}

theorem logBasis_apply (i : Fin (rank F)) :
    logBasis F i = logEmbedding F (Additive.ofMul (fundSystem F i)) := by
  rw [logEmbedding_fundSystem, logBasis, Module.Basis.ofZLatticeBasis_apply]

theorem basisConst_nonneg : 0 ≤ basisConst F :=
  mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem bound_nonneg : 0 ≤ bound F := by
  have := basisConst_nonneg (F := F)
  unfold bound; positivity

theorem weightOf_of_isReal (b : InfinitePlace F → ℤ) {w : InfinitePlace F} (hw : IsReal w) : weightOf F b w = 0 := by
  simp [weightOf, hw]

theorem torsionOrder_dvd_weightOf (b : InfinitePlace F → ℤ) (w : InfinitePlace F) :
    (torsionOrder F : ℤ) ∣ weightOf F b w := by
  unfold weightOf; split_ifs
  · exact dvd_zero _
  · exact dvd_mul_right _ _

theorem abs_weightOf_sub_le (b : InfinitePlace F → ℤ) {w : InfinitePlace F} (hw : IsComplex w) :
    (|weightOf F b w - b w| : ℝ) ≤ (torsionOrder F : ℝ) := by
  have hω : (0 : ℤ) < (torsionOrder F : ℤ) := by exact_mod_cast torsionOrder_pos F
  have hnr : ¬ IsReal w := not_isReal_iff_isComplex.mpr hw
  have e : weightOf F b w - b w = -(b w % (torsionOrder F : ℤ)) := by
    have := Int.emod_add_mul_ediv (b w) (torsionOrder F : ℤ)
    simp only [weightOf, hnr, if_false]
    linarith
  have h1 : 0 ≤ b w % (torsionOrder F : ℤ) := Int.emod_nonneg _ hω.ne'
  have h2 : b w % (torsionOrder F : ℤ) < (torsionOrder F : ℤ) := Int.emod_lt_of_pos _ hω
  have h3 : |weightOf F b w - b w| ≤ (torsionOrder F : ℤ) := by
    rw [e, abs_neg, abs_of_nonneg h1]; exact h2.le
  exact_mod_cast h3

theorem norm_prod_sgnC_zpow_mixedEmbedding (m : InfinitePlace F → ℤ) (u : (𝓞 F)ˣ) :
    ‖∏ w : InfinitePlace F, sgnC F w (mixedEmbedding F ((u : 𝓞 F) : F)) ^ (m w)‖ = 1 := by
  have hunit : IsUnit (mixedEmbedding F ((u : 𝓞 F) : F)) :=
    (isUnit_iff_ne_zero.mpr (Units.coe_ne_zero u)).map (mixedEmbedding F)
  rw [norm_prod]
  exact Finset.prod_eq_one fun w _ => by rw [norm_zpow, norm_sgnC w hunit, one_zpow]

theorem archV_mixedEmbedding_of_mem_torsion (τ : InfinitePlace F → ℝ) (b : InfinitePlace F → ℤ)
    {ζ : (𝓞 F)ˣ} (hζ : ζ ∈ torsion F) :
    archV F τ (weightOf F b) (mixedEmbedding F ((ζ : 𝓞 F) : F)) = 1 := by
  have hw1 : ∀ w : InfinitePlace F, w ((ζ : 𝓞 F) : F) = 1 := (mem_torsion F).mp hζ
  have hphase : phase F τ (mixedEmbedding F ((ζ : 𝓞 F) : F)) = 0 := by
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [logAll_mixedEmbedding, hw1 w, Real.log_one, mul_zero, mul_zero]
  have hpow : ∀ w : InfinitePlace F, (w.embedding ((ζ : 𝓞 F) : F)) ^ (torsionOrder F) = 1 := fun w => by
    have h1 : (⟨ζ, hζ⟩ : torsion F) ^ (torsionOrder F) = 1 := by
      rw [torsionOrder]; exact pow_card_eq_one'
    have h2 : ζ ^ (torsionOrder F) = 1 := by
      have := congrArg (fun x : torsion F => (x : (𝓞 F)ˣ)) h1
      simpa using this
    have h3 : (((ζ : 𝓞 F) : F)) ^ (torsionOrder F) = 1 := by
      have h4 : ((ζ ^ torsionOrder F : (𝓞 F)ˣ) : 𝓞 F) = 1 := by rw [h2]; rfl
      rw [Units.val_pow_eq_pow_val] at h4
      have h5 := congrArg (algebraMap (𝓞 F) F) h4
      simpa using h5
    rw [← map_pow, h3, map_one]
  have hsgn : ∀ w : InfinitePlace F, sgnC F w (mixedEmbedding F ((ζ : 𝓞 F) : F)) ^ (weightOf F b w) = 1 := by
    intro w
    rw [sgnC_mixedEmbedding, hw1 w, Complex.ofReal_one, inv_one, mul_one]
    obtain ⟨k, hk⟩ := torsionOrder_dvd_weightOf b w
    rw [hk, zpow_mul, zpow_natCast, hpow w, one_zpow]
  rw [archV, hphase, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  exact Finset.prod_eq_one fun w _ => hsgn w

theorem phase_mixedEmbedding (τ : InfinitePlace F → ℝ) (u : (𝓞 F)ˣ) :
    phase F τ (mixedEmbedding F ((u : 𝓞 F) : F)) =
      ∑ w : InfinitePlace F, τ w * ((mult w : ℝ) * Real.log (w ((u : 𝓞 F) : F))) := by
  simp only [phase, logAll_mixedEmbedding]

theorem phase_const_mixedEmbedding (c : ℝ) (u : (𝓞 F)ˣ) :
    phase F (fun _ => c) (mixedEmbedding F ((u : 𝓞 F) : F)) = 0 := by
  rw [phase_mixedEmbedding, ← Finset.mul_sum, sum_mult_mul_log u, mul_zero]

theorem phase_extend_mixedEmbedding (Δ : {w : InfinitePlace F // w ≠ w₀} → ℝ) (u : (𝓞 F)ˣ) :
    phase F (fun w => if hw : w = w₀ then 0 else Δ ⟨w, hw⟩) (mixedEmbedding F ((u : 𝓞 F) : F)) =
      ∑ w : {w : InfinitePlace F // w ≠ w₀}, Δ w * logEmbedding F (Additive.ofMul u) w := by
  rw [phase_mixedEmbedding,
    Fintype.sum_eq_add_sum_subtype_ne (fun w : InfinitePlace F =>
      (if hw : w = w₀ then (0 : ℝ) else Δ ⟨w, hw⟩) * ((mult w : ℝ) * Real.log (w ((u : 𝓞 F) : F)))) w₀]
  have e0 : (if hw : (w₀ : InfinitePlace F) = w₀ then (0 : ℝ) else Δ ⟨w₀, hw⟩) *
      ((mult (w₀ : InfinitePlace F) : ℝ) * Real.log (w₀ ((u : 𝓞 F) : F))) = 0 := by
    rw [dif_pos rfl, zero_mul]
  rw [e0, zero_add]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dif_neg w.2, logEmbedding_component]

theorem linearForm_apply_eq_sum (ℓ : logSpace F →ₗ[ℝ] ℝ) (v : logSpace F) :
    ℓ v = ∑ w : {w : InfinitePlace F // w ≠ w₀}, ℓ (Pi.single w 1) * v w := by
  conv_lhs => rw [show v = ∑ w, v w • (Pi.single w (1 : ℝ) : logSpace F) from (Finset.univ_sum_single v).symm.trans
    (Finset.sum_congr rfl fun w _ => by ext j; simp [Pi.single_apply])]
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem abs_constr_single_le (δ : Fin (rank F) → ℝ) (hδ : ∀ i, |δ i| ≤ Real.pi)
    (w : {w : InfinitePlace F // w ≠ w₀}) :
    |(logBasis F).constr ℝ δ (Pi.single w 1)| ≤ basisConst F := by
  rw [Module.Basis.constr_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  calc |∑ i, (logBasis F).repr (Pi.single w 1) i • δ i|
      ≤ ∑ i, |(logBasis F).repr (Pi.single w 1) i • δ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(logBasis F).repr (Pi.single w 1) i| * |δ i| := Finset.sum_congr rfl fun i _ => by
        rw [smul_eq_mul, abs_mul]
    _ ≤ ∑ i, |(logBasis F).repr (Pi.single w 1) i| * Real.pi :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)
    _ = Real.pi * ∑ i, |(logBasis F).repr (Pi.single w 1) i| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ basisConst F := by
        unfold basisConst
        refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
        exact Finset.single_le_sum (f := fun w' : {w : InfinitePlace F // w ≠ w₀} =>
          ∑ i : Fin (rank F), |(logBasis F).repr (Pi.single w' 1) i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ w)

theorem exists_param_partialChar_unitsIdele_eq_one (σ : InfinitePlace F → ℝ) (b : InfinitePlace F → ℤ) :
    ∃ τ : InfinitePlace F → ℝ,
      (∀ w, |τ w - σ w| ≤ 2 * basisConst F) ∧
      (∑ w : InfinitePlace F, (mult w : ℝ) * (τ w - σ w) = 0) ∧
      ∀ u : (𝓞 F)ˣ, partialChar F τ (weightOf F b) (unitsIdele F u) = 1 := by
  set m : InfinitePlace F → ℤ := weightOf F b with hm

  set d : Fin (rank F) → ℂ := fun i =>
    ((∏ w : InfinitePlace F, sgnC F w (mixedEmbedding F ((fundSystem F i : 𝓞 F) : F)) ^ (m w)) *
      Complex.exp ((phase F σ (mixedEmbedding F ((fundSystem F i : 𝓞 F) : F)) : ℂ) * Complex.I))⁻¹ with hd
  have hd1 : ∀ i, ‖d i‖ = 1 := fun i => by
    rw [hd]; dsimp only
    rw [norm_inv, norm_mul, norm_prod_sgnC_zpow_mixedEmbedding, Complex.norm_exp_ofReal_mul_I, one_mul, inv_one]
  set δ : Fin (rank F) → ℝ := fun i => Complex.arg (d i) with hδ
  have hδπ : ∀ i, |δ i| ≤ Real.pi := fun i => Complex.abs_arg_le_pi (d i)
  set ℓ : logSpace F →ₗ[ℝ] ℝ := (logBasis F).constr ℝ δ with hℓ
  set Δ : {w : InfinitePlace F // w ≠ w₀} → ℝ := fun w => ℓ (Pi.single w 1) with hΔ
  set Δ' : InfinitePlace F → ℝ := fun w => if hw : w = w₀ then 0 else Δ ⟨w, hw⟩ with hΔ'
  set c : ℝ := -(∑ w : InfinitePlace F, (mult w : ℝ) * Δ' w) / (∑ w : InfinitePlace F, (mult w : ℝ)) with hc
  have hΔb : ∀ w, |Δ' w| ≤ basisConst F := fun w => by
    rw [hΔ']; dsimp only
    split_ifs with hw
    · rw [abs_zero]; exact basisConst_nonneg
    · exact abs_constr_single_le δ hδπ ⟨w, hw⟩
  have hmultpos : (0 : ℝ) < ∑ w : InfinitePlace F, (mult w : ℝ) := by
    have h : ((∑ w : InfinitePlace F, mult w : ℕ) : ℝ) = ∑ w : InfinitePlace F, (mult w : ℝ) := by push_cast; rfl
    rw [← h, sum_mult_eq]
    exact_mod_cast Module.finrank_pos
  have hcb : |c| ≤ basisConst F := by
    rw [hc, abs_div, abs_neg, abs_of_pos hmultpos, div_le_iff₀ hmultpos]
    calc |∑ w : InfinitePlace F, (mult w : ℝ) * Δ' w|
        ≤ ∑ w : InfinitePlace F, |(mult w : ℝ) * Δ' w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w : InfinitePlace F, basisConst F * (mult w : ℝ) := Finset.sum_le_sum fun w _ => by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hΔb w) (Nat.cast_nonneg _)
      _ = basisConst F * ∑ w : InfinitePlace F, (mult w : ℝ) := by rw [Finset.mul_sum]
  refine ⟨fun w => σ w + Δ' w + c, fun w => ?_, ?_, fun u => ?_⟩
  ·
    have e : σ w + Δ' w + c - σ w = Δ' w + c := by ring
    rw [e]
    calc |Δ' w + c| ≤ |Δ' w| + |c| := abs_add_le _ _
      _ ≤ basisConst F + basisConst F := add_le_add (hΔb w) hcb
      _ = 2 * basisConst F := by ring
  ·
    have e : ∀ w : InfinitePlace F, (mult w : ℝ) * (σ w + Δ' w + c - σ w) = (mult w : ℝ) * Δ' w + c * (mult w : ℝ) :=
      fun w => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hc, div_mul_cancel₀ _ hmultpos.ne', add_neg_cancel]
  ·
    set Φ : (𝓞 F)ˣ →* ℂˣ := (partialChar F (fun w => σ w + Δ' w + c) m).comp (unitsIdele F) with hΦ
    have hΦval : ∀ u : (𝓞 F)ˣ, ((Φ u : ℂˣ) : ℂ) =
        archV F (fun w => σ w + Δ' w + c) m (mixedEmbedding F ((u : 𝓞 F) : F)) := fun u =>
      partialChar_unitsIdele_val _ m u
    have hτsplit : (fun w => σ w + Δ' w + c) = σ + Δ' + fun _ => c := by
      funext w; simp
    have hΦtors : ∀ t : (𝓞 F)ˣ, t ∈ torsion F → Φ t = 1 := by
      intro t ht
      apply Units.ext
      rw [hΦval, hm, archV_mixedEmbedding_of_mem_torsion _ b ht, Units.val_one]
    have hΦfund : ∀ i : Fin (rank F), Φ (fundSystem F i) = 1 := by
      intro i
      apply Units.ext
      set x := mixedEmbedding F ((fundSystem F i : 𝓞 F) : F) with hx
      have hℓi : ℓ (logEmbedding F (Additive.ofMul (fundSystem F i))) = δ i := by
        rw [← logBasis_apply, hℓ, Module.Basis.constr_basis]
      have hΔsum : phase F Δ' x = δ i := by
        rw [hx, hΔ', phase_extend_mixedEmbedding Δ (fundSystem F i), ← hℓi, linearForm_apply_eq_sum]
      have hphase : phase F (fun w => σ w + Δ' w + c) x = phase F σ x + δ i := by
        rw [hτsplit, phase_add, phase_add, hΔsum, hx, phase_const_mixedEmbedding c, add_zero]
      have hexp : Complex.exp ((δ i : ℂ) * Complex.I) = d i := by
        have := Complex.norm_mul_exp_arg_mul_I (d i)
        rwa [hd1, Complex.ofReal_one, one_mul] at this
      have hne : (∏ w : InfinitePlace F, sgnC F w x ^ (m w)) *
          Complex.exp ((phase F σ x : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (norm_ne_zero_iff.mp (by rw [hx, norm_prod_sgnC_zpow_mixedEmbedding]; exact one_ne_zero))
          (Complex.exp_ne_zero _)
      rw [hΦval, Units.val_one, ← hx, archV, hphase, Complex.ofReal_add, add_mul, Complex.exp_add, hexp, hd]
      dsimp only
      rw [← hx, ← mul_assoc]
      exact mul_inv_cancel₀ hne
    have hker : (⊤ : Subgroup (𝓞 F)ˣ) ≤ Φ.ker := by
      rw [← closure_fundSystem_sup_torsion_eq_top, sup_le_iff, Subgroup.closure_le]
      exact ⟨by rintro _ ⟨i, rfl⟩; exact hΦfund i, fun t ht => hΦtors t ht⟩
    exact hker (Subgroup.mem_top u)

end Interpolation

section Local

variable {F : Type} [Field F] [NumberField F]

open IsDedekindDomain.FiniteAdeleRing

theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_archMixed_val :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((archMixed F x : (mixedSpace F)ˣ) : mixedSpace F) :=
  show Continuous fun x : (AdeleRing (𝓞 F) F)ˣ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x : AdeleRing (𝓞 F) F).1) from
    continuous_ringEquiv_mixedSpace.comp (continuous_fst.comp Units.continuous_val)

theorem continuous_finPart : Continuous (finPart F) :=
  Continuous.units_map _ (continuous_adeleFin (𝓞 F) F)

theorem isOpen_unitPartIdeles : IsOpen ((unitPartIdeles F : Subgroup (AdeleRing (𝓞 F) F)ˣ) : Set (AdeleRing (𝓞 F) F)ˣ) :=
  (isOpen_unitIdeles F).preimage continuous_finPart

theorem continuous_of_eq_archV (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ)
    (hη : ∀ x : (AdeleRing (𝓞 F) F)ˣ, x ∈ unitPartIdeles F →
      ((η x : ℂˣ) : ℂ) = archV F τ m ((archMixed F x : (mixedSpace F)ˣ) : mixedSpace F)) :
    Continuous η := by
  have hg : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ =>
      archV F τ m ((archMixed F x : (mixedSpace F)ˣ) : mixedSpace F) :=
    (continuousOn_archV (τ := τ) (m := m)).comp_continuous continuous_archMixed_val
      (fun x => (archMixed F x).isUnit)
  have hval : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((η x : ℂˣ) : ℂ) := by
    refine continuous_of_continuousAt_one ((Units.coeHom ℂ).comp η) ?_
    have hW := isOpen_unitPartIdeles (F := F)
    have h1W : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ ((unitPartIdeles F : Subgroup (AdeleRing (𝓞 F) F)ˣ) : Set _) := one_mem _
    refine (hg.continuousAt).congr ?_
    exact Filter.eventuallyEq_of_mem (hW.mem_nhds h1W) (fun x hx => (hη x hx).symm)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have e : (fun x : (AdeleRing (𝓞 F) F)ˣ => (((η x)⁻¹ : ℂˣ) : ℂ)) =
      fun x : (AdeleRing (𝓞 F) F)ˣ => ((η x⁻¹ : ℂˣ) : ℂ) := by
    funext x; rw [map_inv]
  rw [e]
  exact hval.comp continuous_inv

noncomputable def circleOf {S : Type*} [Monoid S] (f : S →* ℂˣ) (hf : ∀ s : S, ‖((f s : ℂˣ) : ℂ)‖ = 1) :
    S →* Circle where
  toFun s := ⟨((f s : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hf s)⟩
  map_one' := Circle.ext (by simp)
  map_mul' a b := Circle.ext (by simp)

theorem coe_circleOf {S : Type*} [Monoid S] (f : S →* ℂˣ) (hf : ∀ s : S, ‖((f s : ℂˣ) : ℂ)‖ = 1) (s : S) :
    ((circleOf f hf s : Circle) : ℂ) = ((f s : ℂˣ) : ℂ) := rfl

theorem finIncl_localUnit_mem_unitPartIdeles (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (ht' : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) (localUnit (𝓞 F) F v t) ∈
      unitPartIdeles F := by
  rw [mem_unitPartIdeles_iff, mem_unitIdeles_iff]
  have hfin : finPart F (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
      (localUnit (𝓞 F) F v t)) = localUnit (𝓞 F) F v t := Units.ext rfl
  rw [hfin]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v (t : v.adicCompletion F) w ∈ _
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact ht
    · rw [Function.update_of_ne hw]; exact one_mem _
  · rw [← map_inv]
    show Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) w ∈ _
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact ht'
    · rw [Function.update_of_ne hw]; exact one_mem _

theorem archMixed_finIncl (a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((archMixed F (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) a) :
      (mixedSpace F)ˣ) : mixedSpace F) = 1 := by
  rw [archMixed_apply_val]
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 1 = 1
  exact map_one _

theorem archUnitHom_mem_unitPartIdeles (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    archUnitHom w x ∈ unitPartIdeles (F := F) := by
  rw [mem_unitPartIdeles_iff]
  have hfin : finPart F (archUnitHom w x) = 1 := Units.ext rfl
  rw [hfin]; exact one_mem _

theorem evalC_archMixed_archUnitHom_self (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    evalC F w ((archMixed F (archUnitHom w x) : (mixedSpace F)ˣ) : mixedSpace F) =
      Completion.extensionEmbedding w (x : w.Completion) := by
  rw [evalC_archMixed, archUnitHom_apply, archCentralUnit_fst_self]

theorem evalC_archMixed_archUnitHom_of_ne (w : InfinitePlace F) (x : (w.Completion)ˣ) {w' : InfinitePlace F}
    (hw' : w' ≠ w) :
    evalC F w' ((archMixed F (archUnitHom w x) : (mixedSpace F)ˣ) : mixedSpace F) = 1 := by
  rw [evalC_archMixed, archUnitHom_apply, archCentralUnit_fst_of_ne w x hw', map_one]

theorem archV_archMixed_archUnitHom (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ)
    (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    archV F τ m ((archMixed F (archUnitHom w x) : (mixedSpace F)ˣ) : mixedSpace F) =
      (Completion.extensionEmbedding w (x : w.Completion) *
          ((‖Completion.extensionEmbedding w (x : w.Completion)‖ : ℂ))⁻¹) ^ (m w) *
        Complex.exp (((τ w * ((mult w : ℝ) * Real.log ‖Completion.extensionEmbedding w (x : w.Completion)‖) : ℝ) : ℂ) *
          Complex.I) := by
  set X := ((archMixed F (archUnitHom w x) : (mixedSpace F)ˣ) : mixedSpace F) with hX
  have hprod : ∏ w' : InfinitePlace F, sgnC F w' X ^ (m w') = sgnC F w X ^ (m w) := by
    refine Finset.prod_eq_single w (fun w' _ hw' => ?_) (fun h => absurd (Finset.mem_univ w) h)
    rw [sgnC, hX, evalC_archMixed_archUnitHom_of_ne w x hw', norm_one, Complex.ofReal_one, inv_one, mul_one, one_zpow]
  have hsum : phase F τ X = τ w * ((mult w : ℝ) * Real.log ‖Completion.extensionEmbedding w (x : w.Completion)‖) := by
    rw [phase]
    rw [Finset.sum_eq_single w (fun w' _ hw' => ?_) (fun h => absurd (Finset.mem_univ w) h)]
    · rw [logAll, hX, evalC_archMixed_archUnitHom_self]
    · rw [logAll, hX, evalC_archMixed_archUnitHom_of_ne w x hw', norm_one, Real.log_one, mul_zero, mul_zero]
  rw [archV, hprod, hsum, sgnC, hX, evalC_archMixed_archUnitHom_self]

theorem norm_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ideleNorm_archUnitHom (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w x) = ‖Completion.extensionEmbedding w (x : w.Completion)‖ ^ (mult w) := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one F (archUnitHom w x) rfl,
    Finset.prod_eq_single w (fun w' _ hw' => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [archUnitHom_apply, archCentralUnit_fst_self, norm_extensionEmbedding]
  · rw [archUnitHom_apply, archCentralUnit_fst_of_ne w x hw', norm_one, one_pow]

end Local

section Main

variable (F : Type) [Field F] [NumberField F]

open IsDedekindDomain.FiniteAdeleRing

theorem main :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (σ : InfinitePlace F → ℝ) (b : InfinitePlace F → ℤ),
    ∃ (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ),
      IsUnitaryChar (𝓞 F) F η ∧ IsIdeleClassChar (𝓞 F) F η ∧ Continuous η ∧
      (∀ v : HeightOneSpectrum (𝓞 F), IsUnramifiedCharAt η v) ∧
      (∀ (w : InfinitePlace F) (x : (w.Completion)ˣ),
        0 < (Completion.extensionEmbedding w (x : w.Completion)).re →
        (Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
        ((archLocalChar η w x : ℂˣ) : ℂ) =
          (((ideleNorm F (archUnitHom w x)) : ℝ) : ℂ) ^ (((τ w : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (w : InfinitePlace F) (x : (w.Completion)ˣ),
        ‖Completion.extensionEmbedding w (x : w.Completion)‖ = 1 →
        ((archLocalChar η w x : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (x : w.Completion)) ^ (m w)) ∧
      (∀ w : InfinitePlace F, w.IsReal → m w = 0) ∧
      (∀ w : InfinitePlace F, |τ w - σ w| ≤ B) ∧
      (∀ w : InfinitePlace F, w.IsComplex → (|m w - b w| : ℝ) ≤ B) ∧
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (τ w - σ w) = 0 := by
  refine ⟨bound F, bound_nonneg, fun σ b => ?_⟩
  obtain ⟨τ, hτB, hτsum, hunits⟩ := exists_param_partialChar_unitsIdele_eq_one (F := F) σ b
  set m : InfinitePlace F → ℤ := weightOf F b with hm
  set Ψ : ↥(unitPartIdeles F) →* ℂˣ := partialChar F τ m with hΨ
  have hΨ1 : ∀ x : ↥(unitPartIdeles F), ‖((Ψ x : ℂˣ) : ℂ)‖ = 1 := fun x => by
    rw [hΨ, partialChar_apply_val, norm_archV (archMixed F _).isUnit]

  have hdesc : ∀ x : ↥(unitPartIdeles F), (x : (AdeleRing (𝓞 F) F)ˣ) ∈ (prin F).range →
      circleOf Ψ hΨ1 x = 1 := by
    rintro x ⟨k, hk⟩
    have hk' : prin F k ∈ unitPartIdeles F := by rw [hk]; exact x.2
    obtain ⟨u, rfl⟩ := exists_unitsF_eq_of_mem hk'
    have hx : x = unitsIdele F u := Subtype.ext hk.symm
    apply Circle.ext
    rw [coe_circleOf, hx, hΨ, hm, hunits u]
    rfl

  obtain ⟨ηc, hηP, hηU⟩ := exists_monoidHom_extend_trivial (prin F).range (unitPartIdeles F) (circleOf Ψ hΨ1) hdesc
  set η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := Circle.toUnits.comp ηc with hη
  have hηval : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((η x : ℂˣ) : ℂ) = ((ηc x : Circle) : ℂ) := fun x => rfl
  have hηU' : ∀ (x : (AdeleRing (𝓞 F) F)ˣ), x ∈ unitPartIdeles F →
      ((η x : ℂˣ) : ℂ) = archV F τ m ((archMixed F x : (mixedSpace F)ˣ) : mixedSpace F) := by
    intro x hx
    have h : ηc x = circleOf Ψ hΨ1 ⟨x, hx⟩ := hηU ⟨x, hx⟩
    rw [hηval, h, coe_circleOf, hΨ, partialChar_apply_val]
  refine ⟨η, τ, m, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hτsum⟩
  ·
    intro x
    rw [hηval]; exact Circle.norm_coe _
  ·
    intro u
    have h1 := hηP (prin F u) ⟨u, rfl⟩
    apply Units.ext
    show ((η (prin F u) : ℂˣ) : ℂ) = 1
    rw [hηval, h1]; rfl
  ·
    exact continuous_of_eq_archV η τ m hηU'
  ·
    intro v t ht ht'
    apply Units.ext
    rw [localChar_apply, hηU' _ (finIncl_localUnit_mem_unitPartIdeles v t ht ht'), archMixed_finIncl, archV_one,
      Units.val_one]
  ·
    intro w x hre him
    set z : ℂ := Completion.extensionEmbedding w (x : w.Completion) with hz
    have hzn : ‖z‖ = z.re := by
      rw [Complex.norm_def, Complex.normSq_apply, him, mul_zero, add_zero, Real.sqrt_mul_self hre.le]
    have hzr : z = ((‖z‖ : ℝ) : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re, hzn]) (by rw [Complex.ofReal_im, him])
    have hzpos : 0 < ‖z‖ := by rw [hzn]; exact hre
    have hzne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
    rw [archLocalChar, MonoidHom.comp_apply, hηU' _ (archUnitHom_mem_unitPartIdeles w x), archV_archMixed_archUnitHom,
      ideleNorm_archUnitHom, ← hz]
    have hsgn : z * ((‖z‖ : ℂ))⁻¹ = 1 := by
      rw [← hzr]; exact mul_inv_cancel₀ (by rw [hzr]; exact hzne)
    rw [hsgn, one_zpow, one_mul, Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hzpos _).ne'),
      ← Complex.ofReal_log (pow_pos hzpos _).le, Real.log_pow]
    congr 1
    push_cast
    ring
  ·
    intro w x h1
    set z : ℂ := Completion.extensionEmbedding w (x : w.Completion) with hz
    rw [archLocalChar, MonoidHom.comp_apply, hηU' _ (archUnitHom_mem_unitPartIdeles w x), archV_archMixed_archUnitHom,
      ← hz, h1, Real.log_one, mul_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      Complex.ofReal_one, inv_one, mul_one]
  ·
    intro w hw
    rw [hm]; exact weightOf_of_isReal b hw
  ·
    intro w
    refine (hτB w).trans ?_
    unfold bound
    have := (torsionOrder_pos F)
    have h : (0 : ℝ) ≤ (torsionOrder F : ℝ) := Nat.cast_nonneg _
    linarith
  ·
    intro w hw
    refine (abs_weightOf_sub_le b hw).trans ?_
    unfold bound
    have := basisConst_nonneg (F := F)
    linarith

end Main

end R4TwistNormExist
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le.R4TwistNormExist"

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (σ : InfinitePlace K → ℝ) (b : InfinitePlace K → ℤ),
    ∃ (η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ),
      IsUnitaryChar (𝓞 K) K η ∧ IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧
      (∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt η v) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τ v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar η v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → m v = 0) ∧
      (∀ v : InfinitePlace K, |τ v - σ v| ≤ B) ∧
      (∀ v : InfinitePlace K, v.IsComplex → (|m v - b v| : ℝ) ≤ B) ∧
      ∑ v : InfinitePlace K, (v.mult : ℝ) * (τ v - σ v) = 0 :=
  R4TwistNormExist.main K

end S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_exists_isIdeleClassChar_isUnramifiedCharAt_archLocalChar_eq_abs_sub_le (solution)
