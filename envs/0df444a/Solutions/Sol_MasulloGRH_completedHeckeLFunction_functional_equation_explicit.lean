-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_functional_equation_explicit
-- status  : ACCEPTED   (prove)
-- author  : @flashonfire
-- created : 2026-11-21T20:05:14.960837+00:00
-- url     : https://prove2.me/submissions/de70949d-ed70-4999-bd37-c693f5873be3

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain

noncomputable section

namespace MasulloTateBridge

variable {F : Type} [Field F] [NumberField F]

/-- The Hecke character `χ : C_F → U(1)` pulled back to a `ℂˣ`-valued character of the ideles. -/
def lift (χ : MasulloGRH.HeckeCharacter F) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  Circle.toUnits.comp ((χ : MasulloGRH.IdeleClassGroup F →* Circle).comp
    (QuotientGroup.mk' (MasulloGRH.principalIdeles F)))

theorem lift_apply (χ : MasulloGRH.HeckeCharacter F) (g : (AdeleRing (𝓞 F) F)ˣ) :
    ((lift χ g : ℂˣ) : ℂ) = ((χ (QuotientGroup.mk g) : Circle) : ℂ) := rfl

theorem lift_continuous (χ : MasulloGRH.HeckeCharacter F) :
    Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((lift χ z : ℂˣ) : ℂ) := by
  simp only [lift_apply]
  exact continuous_subtype_val.comp (χ.continuous.comp continuous_quotient_mk')

theorem lift_isUnitary (χ : MasulloGRH.HeckeCharacter F) :
    AutomorphicForm.IsUnitaryChar (𝓞 F) F (lift χ) := fun x => by
  rw [lift_apply, Circle.norm_coe]

theorem lift_isIdeleClass (χ : MasulloGRH.HeckeCharacter F) :
    AutomorphicForm.IsIdeleClassChar (𝓞 F) F (lift χ) := fun u => by
  apply Units.ext
  rw [lift_apply]
  have : (QuotientGroup.mk (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u) :
      MasulloGRH.IdeleClassGroup F) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨u, rfl⟩
  erw [this, map_one]
  rfl

theorem lift_inv (χ : MasulloGRH.HeckeCharacter F) : lift χ⁻¹ = (lift χ)⁻¹ := by
  ext g
  simp only [lift_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rfl


open NumberField.AdelicLevel NumberField.TateGlobal

theorem ideleSingle_eq (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    MasulloGRH.ideleSingle v x = Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v x) := by
  classical
  apply Units.ext
  refine Prod.ext rfl ?_
  apply RestrictedProduct.ext
  intro w
  change ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletion F)ˣ) v x w :
      (w.adicCompletion F)ˣ) : w.adicCompletion F) =
    Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v
      (x : v.adicCompletion F) w
  by_cases h : w = v
  · subst h; simp
  · rw [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]; rfl

theorem localComponent_eq (χ : MasulloGRH.HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) :
    χ.localComponent v x = ((localChar (lift χ) v x : ℂˣ) : ℂ) := by
  unfold MasulloGRH.HeckeCharacter.localComponent
  rw [localChar_apply, lift_apply, ideleSingle_eq]

theorem val_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    Valued.v (t : v.adicCompletion F) = 1 ↔
      ((t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
        ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  have hne : Valued.v (t : v.adicCompletion F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact t.ne_zero
  constructor
  · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    have := mul_le_mul' (le_refl (Valued.v (t : v.adicCompletion F))) h2
    rwa [mul_inv_cancel₀ hne, mul_one] at this

theorem unram_iff (χ : MasulloGRH.HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    χ.IsUnramifiedAt v ↔ IsUnramifiedCharAt (lift χ) v := by
  constructor
  · intro h t h1 h2
    apply Units.ext
    rw [← localComponent_eq, Units.val_one]
    exact h t ((val_eq_one_iff v t).2 ⟨h1, h2⟩)
  · intro h x hx
    obtain ⟨h1, h2⟩ := (val_eq_one_iff v x).1 hx
    rw [localComponent_eq, h x h1 h2, Units.val_one]

open scoped Classical in
theorem primeValue_eq (χ : MasulloGRH.HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    χ.primeValue v = if IsUnramifiedCharAt (lift χ) v then
      ((lift χ (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ) else 0 := by
  unfold MasulloGRH.HeckeCharacter.primeValue
  by_cases hu : χ.IsUnramifiedAt v
  · have hex : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, MasulloGRH.IsUniformizerAt v x :=
      ⟨hu, ⟨uniformizerUnit F v, valued_uniformizerUnit F v⟩⟩
    rw [dif_pos hex, if_pos ((unram_iff χ v).1 hu)]
    set y := hex.2.choose
    have hy : MasulloGRH.IsUniformizerAt v y := hex.2.choose_spec
    have hπ : MasulloGRH.IsUniformizerAt v (uniformizerUnit F v) := valued_uniformizerUnit F v
    have hunit : localChar (lift χ) v (y * (uniformizerUnit F v)⁻¹) = 1 := by
      apply (unram_iff χ v).1 hu
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_mul, map_mul,
          Units.val_inv_eq_inv_val, map_inv₀]
        unfold MasulloGRH.IsUniformizerAt at hy hπ
        rw [hy, hπ, mul_inv_cancel₀ (WithZero.exp_ne_zero)]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, mul_inv, inv_inv, Units.val_mul,
          map_mul, Units.val_inv_eq_inv_val, map_inv₀]
        unfold MasulloGRH.IsUniformizerAt at hy hπ
        rw [hy, hπ, inv_mul_cancel₀ (WithZero.exp_ne_zero)]
    have hyπ : localChar (lift χ) v y = localChar (lift χ) v (uniformizerUnit F v) := by
      have := congrArg (· * localChar (lift χ) v (uniformizerUnit F v)) hunit
      simp only [map_mul, map_inv, inv_mul_cancel_right, one_mul] at this
      exact this
    rw [localComponent_eq, hyπ]
    rfl
  · have hn : ¬ (χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, MasulloGRH.IsUniformizerAt v x) :=
      fun h => hu h.1
    rw [dif_neg hn, if_neg (fun h => hu ((unram_iff χ v).2 h))]

open scoped Classical in
theorem eulerProduct_eq (χ : MasulloGRH.HeckeCharacter F) (s : ℂ) :
    MasulloGRH.heckeEulerProduct χ s = ∏' v : HeightOneSpectrum (𝓞 F),
      (1 - (if IsUnramifiedCharAt (lift χ) v then
          ((lift χ (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  unfold MasulloGRH.heckeEulerProduct
  congr 1
  funext v
  rw [primeValue_eq]


/-! ### Archimedean places -/

theorem ideleSingleInfinite_eq (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    MasulloGRH.ideleSingleInfinite w x = archUnitHom w x := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w' => ?_) rfl
  change ((Pi.mulSingle (M := fun w : InfinitePlace F => (w.Completion)ˣ) w x w' :
      (w'.Completion)ˣ) : w'.Completion) =
    Function.update (1 : InfiniteAdeleRing F) w (x : w.Completion) w'
  by_cases h : w' = w
  · subst h; simp
  · rw [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]; rfl

theorem localComponentInfinite_eq (χ : MasulloGRH.HeckeCharacter F) (w : InfinitePlace F)
    (x : (w.Completion)ˣ) :
    χ.localComponentInfinite w x = ((archLocalChar (lift χ) w x : ℂˣ) : ℂ) := by
  unfold MasulloGRH.HeckeCharacter.localComponentInfinite
  rw [archLocalChar, MonoidHom.comp_apply, lift_apply, ideleSingleInfinite_eq]

theorem ideleNorm_archUnitHom (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  classical
  rw [ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one F _ rfl]
  rw [Finset.prod_eq_single w]
  · change ‖Function.update (1 : InfiniteAdeleRing F) w (x : w.Completion) w‖ ^ w.mult = _
    rw [Function.update_self]
  · intro b _ hb
    change ‖Function.update (1 : InfiniteAdeleRing F) w (x : w.Completion) b‖ ^ b.mult = 1
    rw [Function.update_of_ne hb]
    change ‖(1 : b.Completion)‖ ^ b.mult = 1
    simp
  · intro h; exact absurd (Finset.mem_univ w) h

theorem norm_extensionEmbedding (w : InfinitePlace F) (y : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w y‖ = ‖y‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y

/-- Every positive real is the image of a unit of `F_w`. -/
theorem exists_unit_real (w : InfinitePlace F) (c : ℝ) (hc : 0 < c) :
    ∃ x : (w.Completion)ˣ, InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) = c := by
  have hy : ∃ y : w.Completion, InfinitePlace.Completion.extensionEmbedding w y = c := by
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw c
      exact ⟨y, by rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hy]⟩
    · exact InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw c
  obtain ⟨y, hy⟩ := hy
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [map_zero] at hy; exact hc.ne' (Complex.ofReal_eq_zero.1 hy.symm)
  exact ⟨Units.mk0 y hy0, hy⟩

theorem cpow_ofReal_exp_mul_I (θ t : ℝ) :
    ((Real.exp θ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) = Complex.exp ((t * θ : ℝ) * Complex.I) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  congr 1
  push_cast
  ring


theorem exp_pi_I_ne_one : Complex.exp ((Real.pi : ℂ) * Complex.I) ≠ 1 := by
  rw [Complex.exp_pi_mul_I]; norm_num

/-- Uniqueness of the archimedean exponent. -/
theorem exponent_unique (w : InfinitePlace F) (f : (w.Completion)ˣ → ℂ) (t t' : ℝ)
    (ht : ∀ x : (w.Completion)ˣ,
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
      f x = ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I))
    (ht' : ∀ x : (w.Completion)ˣ,
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
      f x = ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((t' : ℂ) * Complex.I)) :
    t = t' := by
  by_contra hne
  have hd : t - t' ≠ 0 := sub_ne_zero.2 hne
  set θ : ℝ := Real.pi / (t - t')
  have hm0 : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.2 InfinitePlace.mult_ne_zero
  obtain ⟨x, hx⟩ := exists_unit_real w (Real.exp (θ / w.mult)) (Real.exp_pos _)
  have hnorm : ‖(x : w.Completion)‖ ^ w.mult = Real.exp θ := by
    rw [← norm_extensionEmbedding, hx, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← Real.exp_nat_mul, mul_div_cancel₀ _ hm0]
  have h1 := ht x (by rw [hx, Complex.ofReal_im]) (by rw [hx, Complex.ofReal_re]; exact Real.exp_pos _)
  have h2 := ht' x (by rw [hx, Complex.ofReal_im]) (by rw [hx, Complex.ofReal_re]; exact Real.exp_pos _)
  rw [hnorm, cpow_ofReal_exp_mul_I] at h1 h2
  have h3 : Complex.exp ((t * θ : ℝ) * Complex.I) = Complex.exp ((t' * θ : ℝ) * Complex.I) :=
    h1.symm.trans h2
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
    have hpi : ((t * θ : ℝ) : ℂ) * Complex.I - ((t' * θ : ℝ) : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I := by
      have : (t - t') * θ = Real.pi := by simp only [θ]; field_simp
      rw [← sub_mul, ← Complex.ofReal_sub, ← sub_mul, this]
    rw [← hpi, Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]
  exact exp_pi_I_ne_one h4

/-- Uniqueness of the archimedean weight at a complex place. -/
theorem weight_unique (w : InfinitePlace F) (hw : w.IsComplex) (f : (w.Completion)ˣ → ℂ) (n n' : ℤ)
    (hn : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      f x = (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ n)
    (hn' : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      f x = (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ n') :
    n = n' := by
  by_contra hne
  have hd : ((n - n' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 (sub_ne_zero.2 hne)
  set θ : ℝ := Real.pi / ((n - n' : ℤ) : ℝ)
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
    (Complex.exp ((θ : ℂ) * Complex.I))
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [map_zero] at hy; exact Complex.exp_ne_zero _ hy.symm
  set x : (w.Completion)ˣ := Units.mk0 y hy0
  have hxn : ‖(x : w.Completion)‖ = 1 := by
    rw [← norm_extensionEmbedding]; change ‖InfinitePlace.Completion.extensionEmbedding w y‖ = 1
    rw [hy, Complex.norm_exp_ofReal_mul_I]
  have h1 := (hn x hxn).symm.trans (hn' x hxn)
  change (InfinitePlace.Completion.extensionEmbedding w y) ^ n =
    (InfinitePlace.Completion.extensionEmbedding w y) ^ n' at h1
  rw [hy, ← Complex.exp_int_mul, ← Complex.exp_int_mul] at h1
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
    have hpi : (n : ℂ) * ((θ : ℂ) * Complex.I) - (n' : ℂ) * ((θ : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
      have : ((n - n' : ℤ) : ℝ) * θ = Real.pi := by simp only [θ]; field_simp
      rw [← sub_mul, ← mul_assoc]
      congr 1
      have := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at this ⊢
      exact this
    rw [← hpi, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  exact exp_pi_I_ne_one h4


/-- The archimedean exponent hypothesis of the `TateGlobal` theorems. -/
def HasArchExponent (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : InfinitePlace F → ℝ) : Prop :=
  ∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
    0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
    (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
    ((archLocalChar ψ v x : ℂˣ) : ℂ) =
      (((ideleNorm F (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I)

/-- The archimedean weight hypothesis of the `TateGlobal` theorems. -/
def HasArchWeight (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (m : InfinitePlace F → ℤ) : Prop :=
  ∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
    ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
    ((archLocalChar ψ v x : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)

theorem archExponent_eq (χ : MasulloGRH.HeckeCharacter F) (τ : InfinitePlace F → ℝ)
    (hτ : HasArchExponent (lift χ) τ) (w : InfinitePlace F) : χ.archExponent w = τ w := by
  have hP : ∀ x : (w.Completion)ˣ,
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
      χ.localComponentInfinite w x =
        ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((τ w : ℂ) * Complex.I) := by
    intro x h1 h2
    rw [localComponentInfinite_eq, hτ w x h2 h1, ideleNorm_archUnitHom]
  unfold MasulloGRH.HeckeCharacter.archExponent
  have hex : ∃ t : ℝ, ∀ x : (w.Completion)ˣ,
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
      χ.localComponentInfinite w x =
        ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := ⟨τ w, hP⟩
  rw [dif_pos hex]
  exact exponent_unique w _ _ _ hex.choose_spec hP

theorem archParity_eq (χ : MasulloGRH.HeckeCharacter F) (m : InfinitePlace F → ℤ)
    (hm : HasArchWeight (lift χ) m) (w : InfinitePlace F) :
    χ.archParity w = (m w).natAbs % 2 := by
  have hneg : ‖InfinitePlace.Completion.extensionEmbedding w
      (((-1 : (w.Completion)ˣ)) : w.Completion)‖ = 1 := by simp
  have h := hm w (-1) hneg
  rw [← localComponentInfinite_eq] at h
  have hemb : InfinitePlace.Completion.extensionEmbedding w
      (((-1 : (w.Completion)ˣ)) : w.Completion) = -1 := by simp
  rw [hemb] at h
  unfold MasulloGRH.HeckeCharacter.archParity
  rcases Int.even_or_odd (m w) with he | ho
  · rw [h, he.neg_one_zpow, if_pos rfl]
    exact (Int.natAbs_even.2 he).two_dvd |> Nat.mod_eq_zero_of_dvd |>.symm
  · rw [h, ho.neg_one_zpow, if_neg (by norm_num)]
    exact (Nat.odd_iff.1 (Int.natAbs_odd.2 ho)).symm

theorem archWeight_eq (χ : MasulloGRH.HeckeCharacter F) (m : InfinitePlace F → ℤ)
    (hm : HasArchWeight (lift χ) m) (w : InfinitePlace F) (hw : w.IsComplex) :
    χ.archWeight w = (m w).natAbs := by
  have hQ : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x =
        (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ (m w) := by
    intro x hx
    rw [localComponentInfinite_eq]
    exact hm w x (by rw [norm_extensionEmbedding]; exact hx)
  unfold MasulloGRH.HeckeCharacter.archWeight
  have hex : ∃ n : ℤ, ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x =
        (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ n := ⟨m w, hQ⟩
  rw [dif_pos hex, weight_unique w hw _ _ _ hex.choose_spec hQ]

open scoped Classical in
/-- The archimedean Γ-factor of the `TateGlobal` theorems. -/
def tateGamma (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace F,
    (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
      else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))

open scoped Classical in
/-- The constant relating the two normalisations of `Γ_ℂ`. -/
def gammaConst (F : Type) [Field F] [NumberField F] : ℂ :=
  ∏ v : InfinitePlace F, (if v.IsReal then (1 : ℂ) else 1 / 2)

open scoped Classical in
theorem gammaConst_ne_zero : gammaConst F ≠ 0 := by
  unfold gammaConst
  rw [Finset.prod_ne_zero_iff]
  intro v _
  split_ifs <;> norm_num

open scoped Classical in
theorem gammaFactor_eq (χ : MasulloGRH.HeckeCharacter F) (τ : InfinitePlace F → ℝ)
    (m : InfinitePlace F → ℤ) (hτ : HasArchExponent (lift χ) τ) (hm : HasArchWeight (lift χ) m)
    (s : ℂ) : χ.gammaFactor s = gammaConst F * tateGamma τ m s := by
  unfold MasulloGRH.HeckeCharacter.gammaFactor gammaConst tateGamma
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold MasulloGRH.HeckeCharacter.archLFactor
  rw [archExponent_eq χ τ hτ w]
  by_cases hw : w.IsReal
  · rw [if_pos hw, if_pos hw, if_pos hw, one_mul, archParity_eq χ m hm w, Complex.Gammaℝ]
    congr 2
    ring
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
    rw [if_neg hw, if_neg hw, if_neg hw, archWeight_eq χ m hm w hc, Complex.Gammaℂ]
    ring


/-! ### The inverse character -/

theorem archLocalChar_inv (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : InfinitePlace F)
    (x : (v.Completion)ˣ) :
    ((archLocalChar ψ⁻¹ v x : ℂˣ) : ℂ) = ((archLocalChar ψ v x : ℂˣ) : ℂ)⁻¹ := by
  rw [archLocalChar_apply, archLocalChar_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

theorem hasArchExponent_inv (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (τ : InfinitePlace F → ℝ)
    (h : HasArchExponent ψ τ) : HasArchExponent ψ⁻¹ (fun v => -τ v) := by
  intro v x h1 h2
  rw [archLocalChar_inv, h v x h1 h2, ← Complex.cpow_neg]
  congr 1
  push_cast
  ring

theorem hasArchWeight_inv (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (m : InfinitePlace F → ℤ)
    (h : HasArchWeight ψ m) : HasArchWeight ψ⁻¹ (fun v => -m v) := by
  intro v x hx
  rw [archLocalChar_inv, h v x hx, zpow_neg]

open scoped Classical in
theorem tateGamma_neg (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) (s : ℂ) :
    tateGamma (fun v => -τ v) (fun v => -m v) s = ∏ v : InfinitePlace F,
      (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)) := by
  unfold tateGamma
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Int.natAbs_neg, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]

theorem localChar_inv (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ) : localChar ψ⁻¹ v t = (localChar ψ v t)⁻¹ := rfl

theorem unram_inv_iff (ψ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    IsUnramifiedCharAt ψ⁻¹ v ↔ IsUnramifiedCharAt ψ v := by
  unfold IsUnramifiedCharAt
  simp only [localChar_inv, inv_eq_one]

open scoped Classical in
theorem eulerProduct_inv_eq (χ : MasulloGRH.HeckeCharacter F) (s : ℂ) :
    MasulloGRH.heckeEulerProduct χ⁻¹ s = ∏' v : HeightOneSpectrum (𝓞 F),
      (1 - (if IsUnramifiedCharAt (lift χ) v then
          (((lift χ (AutomorphicForm.uniformizerIdele F v))⁻¹ : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  rw [eulerProduct_eq, lift_inv]
  congr 1
  funext v
  simp only [unram_inv_iff, MonoidHom.inv_apply]

/-! ### Meromorphy of the Γ-factors -/

theorem meromorphicAt_Gamma_comp {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) :
    MeromorphicAt (fun z => Complex.Gamma (g z)) x := by
  have h1 : AnalyticAt ℂ (fun z => (Complex.Gamma (g z))⁻¹) x :=
    (Complex.differentiable_one_div_Gamma.analyticAt (g x)).comp hg
  have heq : (fun z => Complex.Gamma (g z)) = (fun z => (Complex.Gamma (g z))⁻¹)⁻¹ := by
    funext z; simp
  rw [heq]
  exact h1.meromorphicAt.inv

theorem analyticAt_const_cpow_neg {a : ℂ} (ha : a ≠ 0) {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun z => a ^ g z) x := by
  have : Differentiable ℂ (fun z : ℂ => a ^ z) := fun z => (differentiableAt_id).const_cpow (Or.inl ha)
  exact (this.analyticAt (g x)).comp hg

theorem meromorphicAt_Gammaℝ {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) :
    MeromorphicAt (fun z => Complex.Gammaℝ (g z)) x := by
  unfold Complex.Gammaℝ
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 : AnalyticAt ℂ (fun z => -g z / 2) x := by fun_prop
  have h2 : AnalyticAt ℂ (fun z => g z / 2) x := by fun_prop
  exact (analyticAt_const_cpow_neg hπ h1).meromorphicAt.mul (meromorphicAt_Gamma_comp h2)

theorem meromorphicAt_Gammaℂ {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) :
    MeromorphicAt (fun z => Complex.Gammaℂ (g z)) x := by
  unfold Complex.Gammaℂ
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  have h1 : AnalyticAt ℂ (fun z => -g z) x := by fun_prop
  exact ((analyticAt_const.mul (analyticAt_const_cpow_neg h2π h1))).meromorphicAt.mul
    (meromorphicAt_Gamma_comp hg)

open scoped Classical in
theorem meromorphicOn_tateGamma (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) :
    MeromorphicOn (tateGamma τ m) Set.univ := by
  intro x _
  unfold tateGamma
  refine MeromorphicAt.fun_prod fun v _ => ?_
  by_cases hv : v.IsReal
  · simp only [if_pos hv]
    exact meromorphicAt_Gammaℝ ((analyticAt_id.add analyticAt_const).add analyticAt_const)
  · simp only [if_neg hv]
    exact meromorphicAt_Gammaℂ ((analyticAt_id.add analyticAt_const).add analyticAt_const)


/-! ### Normal forms -/

open Filter Topology

/-- Identity theorem for meromorphic functions in normal form on `ℂ` (as in the accepted proof of
`MasulloGRH.heckeLFunction_polynomial_growth_on_vertical_strips`). -/
theorem eq_of_mnf {f g : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    (hg : MeromorphicNFOn g Set.univ) (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  set S : Set ℂ := {x | ∀ᶠ y in 𝓝[≠] x, f y = g y} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhdsWithin
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx' : ¬ ∃ᶠ y in 𝓝[≠] x, f y = g y := fun hfr =>
      hx (((hf (Set.mem_univ x)).meromorphicAt.frequently_eq_iff_eventuallyEq
        (hg (Set.mem_univ x)).meromorphicAt).1 hfr)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff] at hx'
    filter_upwards [hx'.eventually_nhds] with y hy
    by_cases hyx : y = x
    · rw [hyx]; exact hx
    · intro hyS
      have h1 : ∀ᶠ z in 𝓝 y, z ≠ x := isOpen_ne.mem_nhds hyx
      have h2 : ∀ᶠ z in 𝓝[≠] y, f z ≠ g z :=
        nhdsWithin_le_nhds ((hy.and h1).mono fun z hz => hz.1 hz.2)
      obtain ⟨z, hz1, hz2⟩ := (h2.and hyS).exists
      exact hz1 hz2
  have h2 : (2 : ℂ) ∈ S := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds (by norm_num)
    exact nhdsWithin_le_nhds (Filter.mem_of_superset hm fun s hs => h s hs)
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨2, h2⟩
  funext x
  have hx : x ∈ S := hS ▸ Set.mem_univ x
  exact (((hf (Set.mem_univ x)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hg (Set.mem_univ x))).1 hx).eq_of_nhds

theorem toMNF_apply_of_analyticAt {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ) {x : ℂ}
    (hx : AnalyticAt ℂ f x) : toMeromorphicNFOn f Set.univ x = f x := by
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf (Set.mem_univ x),
    toMeromorphicNFAt_eq_self.2 hx.meromorphicNFAt]

theorem heckeL_spec (χ : MasulloGRH.HeckeCharacter F)
    (hex : ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = MasulloGRH.heckeEulerProduct χ s) :
    MeromorphicNFOn (MasulloGRH.heckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → MasulloGRH.heckeLFunction χ s = MasulloGRH.heckeEulerProduct χ s := by
  unfold MasulloGRH.heckeLFunction
  rw [dif_pos hex]
  exact hex.choose_spec

/-- Identification of the completed L-function with a meromorphic model `R` that agrees with
`Γ_F · (Euler product)` on `Re s > 1`. -/
theorem completed_eq_on (χ : MasulloGRH.HeckeCharacter F)
    (hex : ∃ L : ℂ → ℂ, MeromorphicNFOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re → L s = MasulloGRH.heckeEulerProduct χ s)
    (hγ : MeromorphicOn χ.gammaFactor Set.univ)
    (R : ℂ → ℂ) (hRm : MeromorphicOn R Set.univ)
    (hR : ∀ s : ℂ, 1 < s.re → AnalyticAt ℂ R s ∧
      χ.gammaFactor s * MasulloGRH.heckeEulerProduct χ s = R s) :
    ∀ s : ℂ, AnalyticAt ℂ R s → MasulloGRH.completedHeckeLFunction χ s = R s := by
  obtain ⟨hNF, hL⟩ := heckeL_spec χ hex
  set f : ℂ → ℂ := fun s => χ.gammaFactor s * MasulloGRH.heckeLFunction χ s
  have hfm : MeromorphicOn f Set.univ := hγ.mul hNF.meromorphicOn
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfR : ∀ s : ℂ, 1 < s.re → f =ᶠ[𝓝 s] R := by
    intro s hs
    filter_upwards [hopen.mem_nhds hs] with t ht
    simp only [f]
    rw [hL t ht]
    exact (hR t ht).2
  have key : toMeromorphicNFOn f Set.univ = toMeromorphicNFOn R Set.univ := by
    refine eq_of_mnf (meromorphicNFOn_toMeromorphicNFOn _ _)
      (meromorphicNFOn_toMeromorphicNFOn _ _) fun s hs => ?_
    have hRa := (hR s hs).1
    rw [toMNF_apply_of_analyticAt hfm (hRa.congr (hfR s hs).symm),
      toMNF_apply_of_analyticAt hRm hRa]
    exact (hfR s hs).eq_of_nhds
  intro s hs
  change toMeromorphicNFOn f Set.univ s = R s
  rw [key, toMNF_apply_of_analyticAt hRm hs]


/-! ### Assembly -/

theorem lift_continuous_units (χ : MasulloGRH.HeckeCharacter F) : Continuous (lift χ) := by
  rw [Units.continuous_iff]
  refine ⟨lift_continuous χ, ?_⟩
  have : (fun x => (((lift χ x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((lift χ x⁻¹ : ℂˣ) : ℂ) := by
    funext x; rw [map_inv]
  rw [this]
  exact (lift_continuous χ).comp continuous_inv

theorem normPowChar_inv (t : ℝ) : (normPowChar F t)⁻¹ = normPowChar F (-t) := by
  ext x
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_normPowChar_apply, coe_normPowChar_apply,
    ← Complex.cpow_neg]
  congr 1; push_cast; ring

theorem lift_inv_eq_normPowChar_iff (χ : MasulloGRH.HeckeCharacter F) (t : ℝ) :
    lift χ⁻¹ = normPowChar F t ↔ lift χ = normPowChar F (-t) := by
  rw [lift_inv]
  constructor
  · intro h; rw [← inv_inv (lift χ), h, normPowChar_inv]
  · intro h; rw [h, normPowChar_inv, neg_neg]

open scoped Classical in
theorem eulerP_inv (χ : MasulloGRH.HeckeCharacter F) (w : ℂ) :
    (∏' v : HeightOneSpectrum (𝓞 F),
      (1 - (if IsUnramifiedCharAt (lift χ⁻¹) v then
          ((lift χ⁻¹ (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) =
    ∏' v : HeightOneSpectrum (𝓞 F),
      (1 - (if IsUnramifiedCharAt (lift χ) v then
          (((lift χ (AutomorphicForm.uniformizerIdele F v))⁻¹ : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  rw [← eulerProduct_eq, eulerProduct_inv_eq]

theorem eventually_ne_punctured (s a : ℂ) : ∀ᶠ t in 𝓝[≠] s, t ≠ a := by
  by_cases h : s = a
  · subst h; exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)

/-- **Hecke–Tate functional equation in Masullo's normalisation**, for number fields in `Type`. -/
theorem functional_equation (χ : MasulloGRH.HeckeCharacter F) :
    ∃ (ε : ℂ) (Nf : ℝ), ‖ε‖ = 1 ∧ 0 < Nf ∧ ∀ s : ℂ,
      MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - s) =
        ε * (Nf : ℂ) ^ (s - 1 / 2) * MasulloGRH.completedHeckeLFunction χ s := by
  classical
  set ψ := lift χ with hψ
  obtain ⟨S, hS⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous F ψ (lift_continuous_units χ)
  obtain ⟨τ, m, hτ, hm, -⟩ := exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F ψ
    (lift_isUnitary χ) (lift_continuous χ)
  have hτ' : HasArchExponent (lift χ⁻¹) (fun v => -τ v) := by
    rw [lift_inv]; exact hasArchExponent_inv ψ τ hτ
  have hm' : HasArchWeight (lift χ⁻¹) (fun v => -m v) := by
    rw [lift_inv]; exact hasArchWeight_inv ψ m hm
  obtain ⟨Nf, hNf, hFE⟩ := exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
    F S (fun v => localChar ψ v)
  have hFE' := hFE ψ (lift_continuous χ) (lift_isUnitary χ) (lift_isIdeleClass χ) hS
    (fun v _ u _ _ => rfl) τ m hτ hm
  have hcont := exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq F ψ
    (lift_continuous χ) (lift_isUnitary χ) (lift_isIdeleClass χ) τ m hτ hm
  have hcont' := exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq F
    (lift χ⁻¹) (lift_continuous χ⁻¹) (lift_isUnitary χ⁻¹) (lift_isIdeleClass χ⁻¹)
    (fun v => -τ v) (fun v => -m v) hτ' hm'
  simp only at hFE' hcont hcont'
  have hγ : χ.gammaFactor = fun s => gammaConst F * tateGamma τ m s :=
    funext (gammaFactor_eq χ τ m hτ hm)
  have hγ' : χ⁻¹.gammaFactor = fun s => gammaConst F * tateGamma (fun v => -τ v) (fun v => -m v) s :=
    funext (gammaFactor_eq χ⁻¹ _ _ hτ' hm')
  have hγm : MeromorphicOn χ.gammaFactor Set.univ := by
    rw [hγ]; exact (MeromorphicOn.const _).mul (meromorphicOn_tateGamma τ m)
  have hγm' : MeromorphicOn χ⁻¹.gammaFactor Set.univ := by
    rw [hγ']; exact (MeromorphicOn.const _).mul (meromorphicOn_tateGamma _ _)
  have hex := MasulloGRH.heckeLFunction_exists_meromorphic_continuation F χ
  have hex' := MasulloGRH.heckeLFunction_exists_meromorphic_continuation F χ⁻¹
  by_cases hnp : ∀ τ₀ : ℝ, ψ ≠ normPowChar F τ₀
  · -- the entire case
    have hnp' : ∀ τ₀ : ℝ, lift χ⁻¹ ≠ normPowChar F τ₀ := fun τ₀ h =>
      hnp (-τ₀) ((lift_inv_eq_normPowChar_iff χ τ₀).1 h)
    obtain ⟨L, Λ, hL, hΛ, hLP, hΛγ⟩ := hcont.1 hnp
    obtain ⟨L', Λd, hL', hΛd, hL'P, hΛdγ⟩ := hcont'.1 hnp'
    obtain ⟨ε, hε, hfe⟩ := hFE'.1 hnp L hL hLP L' hL'
      (fun w hw => (hL'P w hw).trans (eulerP_inv χ w)) Λ Λd hΛ hΛd hΛγ
      (fun s hs => by rw [hΛdγ s hs]; congr 1; exact tateGamma_neg τ m s)
    have hc1 : ∀ s, MasulloGRH.completedHeckeLFunction χ s = gammaConst F * Λ s := by
      intro s
      refine completed_eq_on χ hex hγm (fun s => gammaConst F * Λ s)
        (fun x _ => (analyticAt_const.mul (hΛ.analyticAt x)).meromorphicAt) (fun t ht => ?_) s
        (analyticAt_const.mul (hΛ.analyticAt s))
      refine ⟨analyticAt_const.mul (hΛ.analyticAt t), ?_⟩
      rw [hγ, eulerProduct_eq, ← hLP t ht, mul_assoc, hΛγ t (by linarith)]
      rfl
    have hc2 : ∀ s, MasulloGRH.completedHeckeLFunction χ⁻¹ s = gammaConst F * Λd s := by
      intro s
      refine completed_eq_on χ⁻¹ hex' hγm' (fun s => gammaConst F * Λd s)
        (fun x _ => (analyticAt_const.mul (hΛd.analyticAt x)).meromorphicAt) (fun t ht => ?_) s
        (analyticAt_const.mul (hΛd.analyticAt s))
      refine ⟨analyticAt_const.mul (hΛd.analyticAt t), ?_⟩
      rw [hγ', eulerProduct_eq, ← hL'P t ht, mul_assoc, hΛdγ t (by linarith)]
      rfl
    refine ⟨ε, Nf, hε, hNf, fun s => ?_⟩
    rw [hc1, hc2, hfe]
    ring
  · -- the norm-power case `ψ = ‖·‖^{iτ₀}`
    push Not at hnp
    obtain ⟨τ₀, hτ₀⟩ := hnp
    have hτ₀' : lift χ⁻¹ = normPowChar F (-τ₀) :=
      (lift_inv_eq_normPowChar_iff χ (-τ₀)).2 (by rw [neg_neg]; exact hτ₀)
    obtain ⟨Q, ΛQ, hQ, hΛQ, hQP, hΛQγ⟩ := hcont.2 τ₀ hτ₀
    obtain ⟨Q', ΛQd, hQ', hΛQd, hQ'P, hΛQdγ⟩ := hcont'.2 (-τ₀) hτ₀'
    have hΛQγ' : ∀ s : ℂ, 0 < s.re →
        ΛQ s = (s + ((τ₀ : ℝ) : ℂ) * Complex.I) * (tateGamma τ m s * Q s) := hΛQγ
    have hΛQdγ' : ∀ s : ℂ, 0 < s.re →
        ΛQd s = (s - ((τ₀ : ℝ) : ℂ) * Complex.I) *
          (tateGamma (fun v => -τ v) (fun v => -m v) s * Q' s) := by
      intro s hs; rw [hΛQdγ s hs]; congr 1; push_cast; ring
    have hQ'P' : ∀ w : ℂ, 1 < w.re →
        Q' w = (w - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) * MasulloGRH.heckeEulerProduct χ⁻¹ w := by
      intro w hw; rw [hQ'P w hw, eulerProduct_eq]; congr 1; push_cast; ring
    obtain ⟨ε, hε, hfe⟩ := hFE'.2 τ₀ hτ₀ Q hQ hQP Q' hQ'
      (fun w hw => by rw [hQ'P' w hw, eulerProduct_inv_eq]) ΛQ ΛQd hΛQ hΛQd hΛQγ
      (fun s hs => by rw [hΛQdγ' s hs]; congr 2; exact tateGamma_neg τ m s)
    set a : ℂ := ((τ₀ : ℝ) : ℂ) * Complex.I
    set D : ℂ → ℂ := fun s => (s + a) * (s - (1 - a))
    set D' : ℂ → ℂ := fun t => (t - a) * (t - (1 + a))
    set R : ℂ → ℂ := fun s => gammaConst F * ΛQ s / D s
    set R' : ℂ → ℂ := fun t => gammaConst F * ΛQd t / D' t
    have hDan : ∀ s, AnalyticAt ℂ D s := fun s => by fun_prop
    have hD'an : ∀ s, AnalyticAt ℂ D' s := fun s => by fun_prop
    have hRan : ∀ s, D s ≠ 0 → AnalyticAt ℂ R s := fun s hs =>
      (analyticAt_const.mul (hΛQ.analyticAt s)).div (hDan s) hs
    have hR'an : ∀ t, D' t ≠ 0 → AnalyticAt ℂ R' t := fun t ht =>
      (analyticAt_const.mul (hΛQd.analyticAt t)).div (hD'an t) ht
    have hRm : MeromorphicOn R Set.univ := fun x _ =>
      (analyticAt_const.mul (hΛQ.analyticAt x)).meromorphicAt.div (hDan x).meromorphicAt
    have hR'm : MeromorphicOn R' Set.univ := fun x _ =>
      (analyticAt_const.mul (hΛQd.analyticAt x)).meromorphicAt.div (hD'an x).meromorphicAt
    have hre_ne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h, Complex.zero_re] at hz; linarith
    have hDne : ∀ t : ℂ, 1 < t.re → D t ≠ 0 := by
      intro t ht
      refine mul_ne_zero (hre_ne _ ?_) (hre_ne _ ?_) <;> simp [a] <;> linarith
    have hD'ne : ∀ t : ℂ, 1 < t.re → D' t ≠ 0 := by
      intro t ht
      refine mul_ne_zero (hre_ne _ ?_) (hre_ne _ ?_) <;> simp [a] <;> linarith
    have hc1 : ∀ s, D s ≠ 0 → MasulloGRH.completedHeckeLFunction χ s = R s := by
      intro s hs
      refine completed_eq_on χ hex hγm R hRm (fun t ht => ⟨hRan t (hDne t ht), ?_⟩) s (hRan s hs)
      have hDt := hDne t ht
      rw [hγ]
      simp only [R]
      rw [eq_div_iff hDt, hΛQγ' t (by linarith), eulerProduct_eq, hQP t ht]
      simp only [D, a]
      ring
    have hc2 : ∀ t, D' t ≠ 0 → MasulloGRH.completedHeckeLFunction χ⁻¹ t = R' t := by
      intro t ht
      refine completed_eq_on χ⁻¹ hex' hγm' R' hR'm (fun u hu => ⟨hR'an u (hD'ne u hu), ?_⟩) t (hR'an t ht)
      have hDu := hD'ne u hu
      rw [hγ']
      simp only [R']
      rw [eq_div_iff hDu, hΛQdγ' u (by linarith), hQ'P' u hu]
      simp only [D', a]
      ring
    have hDD : ∀ s, D' (1 - s) = D s := fun s => by simp only [D, D']; ring
    have key : ∀ s, D s ≠ 0 → MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - s) =
        ε * (Nf : ℂ) ^ (s - 1 / 2) * MasulloGRH.completedHeckeLFunction χ s := by
      intro s hs
      rw [hc1 s hs, hc2 (1 - s) (by rw [hDD]; exact hs)]
      simp only [R, R']
      rw [hfe s, hDD]
      ring
    refine ⟨ε, Nf, hε, hNf, fun s => ?_⟩
    by_cases hs : D s ≠ 0
    · exact key s hs
    · have hNF1 : MeromorphicNFOn (MasulloGRH.completedHeckeLFunction χ⁻¹) Set.univ :=
        meromorphicNFOn_toMeromorphicNFOn _ _
      have hNF2 : MeromorphicNFOn (MasulloGRH.completedHeckeLFunction χ) Set.univ :=
        meromorphicNFOn_toMeromorphicNFOn _ _
      have hA : MeromorphicNFAt (fun t => MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - t)) s :=
        (hNF1 (Set.mem_univ (1 - s))).comp_analyticAt (g := fun t => 1 - t) (by fun_prop)
      have hNf0 : (Nf : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNf.ne'
      have hε0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hε; exact zero_ne_one hε
      have hg : AnalyticAt ℂ (fun t => ε * (Nf : ℂ) ^ (t - 1 / 2)) s :=
        analyticAt_const.mul (analyticAt_const_cpow_neg hNf0 (by fun_prop))
      have hg0 : ε * (Nf : ℂ) ^ (s - 1 / 2) ≠ 0 := by
        refine mul_ne_zero hε0 ?_
        rw [Complex.cpow_def_of_ne_zero hNf0]; exact Complex.exp_ne_zero _
      have hB : MeromorphicNFAt (fun t => ε * (Nf : ℂ) ^ (t - 1 / 2) *
          MasulloGRH.completedHeckeLFunction χ t) s :=
        (meromorphicNFAt_mul_iff_right (f := MasulloGRH.completedHeckeLFunction χ) hg hg0).2
          (hNF2 (Set.mem_univ s))
      have hev : (fun t => MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - t)) =ᶠ[𝓝[≠] s]
          (fun t => ε * (Nf : ℂ) ^ (t - 1 / 2) * MasulloGRH.completedHeckeLFunction χ t) := by
        filter_upwards [eventually_ne_punctured s (-a), eventually_ne_punctured s (1 - a)]
          with t h1 h2
        refine key t (mul_ne_zero ?_ (sub_ne_zero.2 h2))
        intro h; exact h1 (eq_neg_of_add_eq_zero_left h)
      exact ((hA.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hB).1 hev).eq_of_nhds

end MasulloTateBridge

theorem solution
    (F : Type) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) :
    ∃ (ε : ℂ) (Nf : ℝ), ‖ε‖ = 1 ∧ 0 < Nf ∧ ∀ s : ℂ,
      MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - s) =
        ε * (Nf : ℂ) ^ (s - 1 / 2) * MasulloGRH.completedHeckeLFunction χ s :=
  MasulloTateBridge.functional_equation χ
