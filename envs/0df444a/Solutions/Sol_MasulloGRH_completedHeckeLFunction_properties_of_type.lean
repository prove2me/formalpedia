-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_properties_of_type
-- status  : ACCEPTED   (prove)
-- author  : @flashonfire
-- created : 2026-11-21T20:26:34.370738+00:00
-- url     : https://prove2.me/submissions/c5121a2f-1f45-4783-9503-0bf06dd9a5cd

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

section


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

end

end

section


open NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.TateGlobal

noncomputable section

namespace MasulloNormCompare

variable {F : Type} [Field F] [NumberField F]

local notation "A" => AdeleRing (𝓞 F) F

/-- The finite component at `w`, as a monoid homomorphism. -/
def compHom (w : HeightOneSpectrum (𝓞 F)) : A →* w.adicCompletion F where
  toFun x := (x.2 : FiniteAdeleRing (𝓞 F) F) w
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The finite component at `w` of an idele, as a unit. -/
def compUnits (w : HeightOneSpectrum (𝓞 F)) : Aˣ →* (w.adicCompletion F)ˣ := Units.map (compHom w)

/-- The archimedean part of an idele, as a unit of the infinite adeles. -/
def archUnits : Aˣ →* (InfiniteAdeleRing F)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

theorem compUnits_val (w : HeightOneSpectrum (𝓞 F)) (g : Aˣ) :
    ((compUnits w g : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
      ((g : A).2 : FiniteAdeleRing (𝓞 F) F) w := rfl

theorem tgNorm_one : ideleNorm F (1 : Aˣ) = 1 := by simp [ideleNorm]

theorem tgNorm_zpow (x : Aˣ) (k : ℤ) : ideleNorm F (x ^ k) = ideleNorm F x ^ k := by
  have hinv : ∀ y : Aˣ, ideleNorm F y⁻¹ = (ideleNorm F y)⁻¹ := by
    intro y
    have h := ideleNorm_mul y⁻¹ y
    rw [inv_mul_cancel, tgNorm_one] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hpow : ∀ (y : Aˣ) (n : ℕ), ideleNorm F (y ^ n) = ideleNorm F y ^ n := by
    intro y n
    induction n with
    | zero => simp [tgNorm_one]
    | succ n ih => rw [pow_succ, ideleNorm_mul, ih, pow_succ]
  rcases k with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact hpow x n
  · rw [zpow_negSucc, hinv, hpow, zpow_negSucc]

theorem tgNorm_prod (s : Finset (HeightOneSpectrum (𝓞 F))) (f : HeightOneSpectrum (𝓞 F) → Aˣ) :
    ideleNorm F (∏ v ∈ s, f v) = ∏ v ∈ s, ideleNorm F (f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tgNorm_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, ideleNorm_mul, ih]

/-- Norm of an element of `F_v` in terms of its valuation. -/
theorem norm_eq_absNorm_zpow (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : x ≠ 0) :
    ‖x‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by rw [Ne, map_eq_zero]; exact hx
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  have : (WithZero.unzero hv).toAdd = WithZero.log (Valued.v x) := by
    conv_rhs => rw [← WithZero.coe_unzero hv]
    rfl
  rw [this]
  push_cast
  rfl


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

/-- Valuation of a unit, as a homomorphism of groups. -/
def valU (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* (WithZero (Multiplicative ℤ))ˣ :=
  Units.map (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom

theorem valU_val (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    ((valU w x : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ)) =
      Valued.v (x : w.adicCompletion F) := rfl

open scoped Classical in
theorem val_compUnits_uniformizerIdele (w v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((compUnits w (AutomorphicForm.uniformizerIdele F v) : (w.adicCompletion F)ˣ) :
      w.adicCompletion F) = if w = v then WithZero.exp (-1 : ℤ) else 1 := by
  rw [compUnits_val]
  change Valued.v (Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v
    ((uniformizerUnit F v : (v.adicCompletion F)ˣ) : v.adicCompletion F) w) = _
  by_cases h : w = v
  · subst h; rw [Function.update_self, if_pos rfl]; exact valued_uniformizerUnit F w
  · rw [Function.update_of_ne h, if_neg h]; exact map_one _

theorem archUnits_uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) :
    archUnits (AutomorphicForm.uniformizerIdele F v) = 1 := Units.ext rfl


/-- **Masullo's idele norm is the Haar modulus `TateGlobal.ideleNorm`.** -/
theorem ideleNorm_eq (g : Aˣ) : MasulloGRH.ideleNorm g = ideleNorm F g := by
  classical
  set c : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ := fun w => compUnits w g with hc
  -- almost all components have valuation one
  have hev : ∀ᶠ w in Filter.cofinite, Valued.v ((c w : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 := by
    have h1 := ((g : A).2).2
    have h2 := ((g⁻¹ : Aˣ) : A).2.2
    filter_upwards [h1, h2] with w hw1 hw2
    refine (val_eq_one_iff w (c w)).2 ⟨hw1, ?_⟩
    have : ((c w)⁻¹ : (w.adicCompletion F)ˣ) = compUnits w g⁻¹ := by rw [hc, map_inv]
    rw [this, compUnits_val]
    exact hw2
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hev).toFinset with hT
  have hnotT : ∀ w, w ∉ T → Valued.v ((c w : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 := by
    intro w hw
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 h)
  set n : HeightOneSpectrum (𝓞 F) → ℤ := fun w =>
    WithZero.log (Valued.v ((c w : (w.adicCompletion F)ˣ) : w.adicCompletion F)) with hn
  have hvc : ∀ w, Valued.v ((c w : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (n w) := by
    intro w
    rw [hn, WithZero.exp_log]
    rw [Ne, map_eq_zero]; exact (c w).ne_zero
  set Y : Aˣ := ∏ w ∈ T, (AutomorphicForm.uniformizerIdele F w) ^ (-n w) with hY
  set a : Aˣ := MulEquiv.prodUnits.symm (archUnits g, 1) with ha
  set u : Aˣ := (a * Y)⁻¹ * g with hu
  have hg : g = a * Y * u := by rw [hu, mul_inv_cancel_left]
  -- the three Haar norms
  have hNa : ideleNorm F a = ∏ w : InfinitePlace F, ‖(g : A).1 w‖ ^ w.mult :=
    ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one F a rfl
  have hNY : ideleNorm F Y = ∏ w ∈ T, ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (n w) := by
    rw [hY, tgNorm_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [tgNorm_zpow, ideleNorm_uniformizerIdele, inv_zpow', neg_neg]
  -- valuations of the components of `u`
  have hvY : ∀ w, Valued.v ((compUnits w Y : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
      if w ∈ T then WithZero.exp (n w) else 1 := by
    intro w
    rw [← valU_val, hY, map_prod, map_prod, Units.coe_prod]
    simp_rw [map_zpow, Units.val_zpow_eq_zpow_val, valU_val, val_compUnits_uniformizerIdele]
    by_cases hw : w ∈ T
    · rw [if_pos hw, Finset.prod_eq_single w]
      · rw [if_pos rfl, ← WithZero.exp_zsmul]; congr 1; simp
      · intro b _ hb; rw [if_neg (Ne.symm hb), one_zpow]
      · intro h; exact absurd hw h
    · rw [if_neg hw, Finset.prod_eq_one]
      intro b hb; rw [if_neg (fun h => hw (by rw [h]; exact hb)), one_zpow]
  have hva : ∀ w, compUnits w a = 1 := fun w => Units.ext rfl
  have hvu : ∀ w, Valued.v ((compUnits w u : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 := by
    intro w
    rw [← valU_val, hu]
    simp only [map_mul, map_inv, hva, one_mul, Units.val_mul, Units.val_inv_eq_inv_val, valU_val]
    rw [hvY]
    by_cases hw : w ∈ T
    · rw [if_pos hw, ← hvc w, inv_mul_cancel₀]
      rw [Ne, map_eq_zero]; exact (c w).ne_zero
    · rw [if_neg hw, inv_one, one_mul]; exact hnotT w hw
  have hNu : ideleNorm F u = 1 := by
    refine ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles F u ?_ ?_
    · have h1 : archUnits u = 1 := by
        rw [hu, map_mul, map_inv, map_mul, hY, map_prod]
        simp_rw [map_zpow, archUnits_uniformizerIdele, one_zpow, Finset.prod_const_one, mul_one]
        rw [ha]
        exact inv_mul_cancel _
      exact congrArg Units.val h1
    · refine ⟨fun w => ?_, fun w => ?_⟩
      · exact ((val_eq_one_iff w (compUnits w u)).1 (hvu w)).1
      · have := ((val_eq_one_iff w (compUnits w u)).1 (hvu w)).2
        rw [← map_inv, compUnits_val] at this
        exact this
  -- Masullo's norm
  have hM : MasulloGRH.ideleNorm g = (∏ w : InfinitePlace F, ‖(g : A).1 w‖ ^ w.mult) *
      ∏ w ∈ T, ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (n w) := by
    unfold MasulloGRH.ideleNorm
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
    · refine Finset.prod_congr rfl fun w _ => ?_
      exact norm_eq_absNorm_zpow w _ (c w).ne_zero
    · intro w hw
      by_contra hwT
      apply hw
      have h1 : ‖((c w : (w.adicCompletion F)ˣ) : w.adicCompletion F)‖ = 1 := by
        rw [FinitePlace.norm_def, hnotT w hwT, map_one]; rfl
      exact h1
  rw [hM]
  conv_rhs => rw [hg]
  rw [ideleNorm_mul, ideleNorm_mul, hNa, hNY, hNu, mul_one]

end MasulloNormCompare

end

end

section


open NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.TateGlobal Filter Topology

noncomputable section

namespace MasulloTateBridge

variable {F : Type} [Field F] [NumberField F]

theorem order_simple_pole (h : ℂ → ℂ) (p : ℂ) (hh : AnalyticAt ℂ h p) (hp : h p ≠ 0) :
    meromorphicOrderAt (fun s => h s / (s - p)) p = -1 := by
  change meromorphicOrderAt (h / fun s : ℂ => s - p) p = -1
  rw [meromorphicOrderAt_div hh.meromorphicAt (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - p) p).meromorphicAt,
    hh.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.2 (Or.inr hp)]
  have : meromorphicOrderAt (fun s : ℂ => s - p) p = 1 := meromorphicOrderAt_id_sub_const
  rw [this]
  rfl

theorem order_zero_of_analytic {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (hx : f x ≠ 0) :
    meromorphicOrderAt f x = 0 := by
  rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.2 (Or.inr hx)]
  rfl

theorem Gammaℂ_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.Gammaℂ z ≠ 0 := by
  unfold Complex.Gammaℂ
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hz)
  rw [Complex.cpow_def_of_ne_zero h2π]; exact Complex.exp_ne_zero _

open scoped Classical in
theorem tateGamma_ne_zero (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) {s : ℂ}
    (hs : 0 < s.re) : tateGamma τ m s ≠ 0 := by
  unfold tateGamma
  rw [Finset.prod_ne_zero_iff]
  intro v _
  by_cases hv : v.IsReal
  · rw [if_pos hv]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.natCast_re]
    have := Nat.cast_nonneg (α := ℝ) ((m v).natAbs % 2)
    linarith
  · rw [if_neg hv]
    refine Gammaℂ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
    have : (0 : ℝ) ≤ ((m v).natAbs : ℝ) * 2 / (2 * 2 + 0 * 0) := by positivity
    norm_num at this ⊢
    positivity

theorem tprod_subtype_empty (f : HeightOneSpectrum (𝓞 F) → ℂ) :
    ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F)))}, f v.1 =
      ∏' v, f v :=
  (Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)).tprod_eq f

theorem lift_eq_normPowChar_of_isNormPower (χ : MasulloGRH.HeckeCharacter F) (t₀ : ℝ)
    (h : χ.IsNormPower t₀) : lift χ = normPowChar F (-t₀) := by
  ext g
  rw [lift_apply, h g, coe_normPowChar_apply, MasulloNormCompare.ideleNorm_eq]
  congr 1; push_cast; ring

theorem isTrivialOnNormOne_of_eq_normPowChar (χ : MasulloGRH.HeckeCharacter F) (τ₀ : ℝ)
    (h : lift χ = normPowChar F τ₀) : χ.IsTrivialOnNormOne := by
  intro g hg
  have h1 : lift χ g = 1 := by
    rw [h]; exact normPowChar_eq_one_of_ideleNorm_eq_one τ₀ (by rw [← MasulloNormCompare.ideleNorm_eq]; exact hg)
  apply Subtype.ext
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
  simpa [lift_apply] using this


/-- The entire case: `χ` is not a norm power. -/
theorem entire_case (χ : MasulloGRH.HeckeCharacter F)
    (hnp : ∀ τ₀ : ℝ, lift χ ≠ normPowChar F τ₀) :
    (∀ s : ℂ, 1 < s.re → MasulloGRH.completedHeckeLFunction χ s =
      χ.gammaFactor s * MasulloGRH.heckeEulerProduct χ s) ∧
    Differentiable ℂ (MasulloGRH.completedHeckeLFunction χ) ∧
    (∀ s : ℂ, 1 ≤ s.re → MasulloGRH.completedHeckeLFunction χ s ≠ 0) := by
  classical
  set ψ := lift χ with hψ
  obtain ⟨τ, m, hτ, hm, -⟩ := exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F ψ
    (lift_isUnitary χ) (lift_continuous χ)
  have hcont := exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq F ψ
    (lift_continuous χ) (lift_isUnitary χ) (lift_isIdeleClass χ) τ m hτ hm
  simp only at hcont
  have hγ : χ.gammaFactor = fun s => gammaConst F * tateGamma τ m s :=
    funext (gammaFactor_eq χ τ m hτ hm)
  have hγm : MeromorphicOn χ.gammaFactor Set.univ := by
    rw [hγ]; exact (MeromorphicOn.const _).mul (meromorphicOn_tateGamma τ m)
  have hex := MasulloGRH.heckeLFunction_exists_meromorphic_continuation F χ
  obtain ⟨L, Λ, hL, hΛ, hLP, hΛγ⟩ := hcont.1 hnp
  have hΛγ' : ∀ s : ℂ, 0 < s.re → Λ s = tateGamma τ m s * L s := hΛγ
  have hval : ∀ t : ℂ, 1 < t.re →
      χ.gammaFactor t * MasulloGRH.heckeEulerProduct χ t = gammaConst F * Λ t := by
    intro t ht
    rw [hγ, eulerProduct_eq, ← hLP t ht, mul_assoc, hΛγ' t (by linarith)]
  have hc1 : ∀ s, MasulloGRH.completedHeckeLFunction χ s = gammaConst F * Λ s := by
    intro s
    exact completed_eq_on χ hex hγm (fun s => gammaConst F * Λ s)
      (fun x _ => (analyticAt_const.mul (hΛ.analyticAt x)).meromorphicAt)
      (fun t ht => ⟨analyticAt_const.mul (hΛ.analyticAt t), hval t ht⟩) s
      (analyticAt_const.mul (hΛ.analyticAt s))
  have hfun : MasulloGRH.completedHeckeLFunction χ = fun s => gammaConst F * Λ s := funext hc1
  refine ⟨fun s hs => (hc1 s).trans (hval s hs).symm, ?_, ?_⟩
  · rw [hfun]; exact (differentiable_const _).mul hΛ
  · intro s hs
    have hχ1 : ∃ x ∈ normOneIdeles F, ψ x ≠ 1 := by
      by_contra h
      push Not at h
      obtain ⟨t, ht⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles F ψ
        (lift_continuous_units χ) (lift_isUnitary χ) h
      exact hnp t ht
    obtain ⟨A, N, hAN⟩ := exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
      F ψ (lift_isIdeleClass χ) (lift_continuous_units χ) (lift_isUnitary χ) hχ1 ∅ L hL
      (fun t ht => by
        rw [hLP t ht]
        exact (tprod_subtype_empty (fun v => (1 - (if IsUnramifiedCharAt ψ v then
          ((ψ (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t)))⁻¹)).symm)
    have hLs : L s ≠ 0 := by
      intro h0
      have := hAN s hs
      rw [h0, norm_zero, mul_zero] at this
      linarith
    rw [hc1, hΛγ' s (by linarith)]
    exact mul_ne_zero gammaConst_ne_zero (mul_ne_zero (tateGamma_ne_zero τ m (by linarith)) hLs)


/-- The norm-power case `lift χ = ‖·‖^{iτ₀}`. -/
theorem normPower_case (χ : MasulloGRH.HeckeCharacter F) (τ₀ : ℝ)
    (hτ₀ : lift χ = normPowChar F τ₀) :
    (∀ s : ℂ, 1 < s.re → MasulloGRH.completedHeckeLFunction χ s =
      χ.gammaFactor s * MasulloGRH.heckeEulerProduct χ s) ∧
    meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) (-(((τ₀ : ℝ) : ℂ) * Complex.I)) = -1 ∧
    meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) (1 - ((τ₀ : ℝ) : ℂ) * Complex.I) = -1 ∧
    (∀ s : ℂ, s ≠ -(((τ₀ : ℝ) : ℂ) * Complex.I) → s ≠ 1 - ((τ₀ : ℝ) : ℂ) * Complex.I →
      AnalyticAt ℂ (MasulloGRH.completedHeckeLFunction χ) s ∧
      (1 ≤ s.re → MasulloGRH.completedHeckeLFunction χ s ≠ 0)) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous F (lift χ)
    (lift_continuous_units χ)
  obtain ⟨τ, m, hτ, hm, -⟩ := exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F (lift χ)
    (lift_isUnitary χ) (lift_continuous χ)
  have hτ' : HasArchExponent (lift χ⁻¹) (fun v => -τ v) := by
    rw [lift_inv]; exact hasArchExponent_inv (lift χ) τ hτ
  have hm' : HasArchWeight (lift χ⁻¹) (fun v => -m v) := by
    rw [lift_inv]; exact hasArchWeight_inv (lift χ) m hm
  obtain ⟨Nf, hNf, hFE⟩ := exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
    F S (fun v => localChar (lift χ) v)
  have hFE' := hFE (lift χ) (lift_continuous χ) (lift_isUnitary χ) (lift_isIdeleClass χ) hS
    (fun v _ u _ _ => rfl) τ m hτ hm
  have hcont := exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq F
    (lift χ) (lift_continuous χ) (lift_isUnitary χ) (lift_isIdeleClass χ) τ m hτ hm
  have hcont' := exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq F
    (lift χ⁻¹) (lift_continuous χ⁻¹) (lift_isUnitary χ⁻¹) (lift_isIdeleClass χ⁻¹)
    (fun v => -τ v) (fun v => -m v) hτ' hm'
  simp only at hFE' hcont hcont'
  have hγ : χ.gammaFactor = fun s => gammaConst F * tateGamma τ m s :=
    funext (gammaFactor_eq χ τ m hτ hm)
  have hγm : MeromorphicOn χ.gammaFactor Set.univ := by
    rw [hγ]; exact (MeromorphicOn.const _).mul (meromorphicOn_tateGamma τ m)
  have hex := MasulloGRH.heckeLFunction_exists_meromorphic_continuation F χ
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
  -- residues do not vanish
  obtain ⟨A1, N1, hA1⟩ := exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar F τ₀ ∅ Q hQ
    (fun s hs => by rw [hQP s hs, hτ₀]; congr 1; exact (tprod_subtype_empty _).symm)
  obtain ⟨A2, N2, hA2⟩ := exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar F (-τ₀) ∅ Q' hQ'
    (fun s hs => by rw [hQ'P s hs, hτ₀']; congr 1; exact (tprod_subtype_empty _).symm)
  have hQne : ∀ w : ℂ, 1 ≤ w.re → Q w ≠ 0 := fun w hw h0 => by
    have := hA1 w hw; rw [h0, norm_zero, mul_zero] at this; linarith
  have hQ'ne : ∀ w : ℂ, 1 ≤ w.re → Q' w ≠ 0 := fun w hw h0 => by
    have := hA2 w hw; rw [h0, norm_zero, mul_zero] at this; linarith
  -- the meromorphic model
  set a : ℂ := ((τ₀ : ℝ) : ℂ) * Complex.I with ha
  have hare : a.re = 0 := by simp [a]
  set D : ℂ → ℂ := fun s => (s + a) * (s - (1 - a))
  set R : ℂ → ℂ := fun s => gammaConst F * ΛQ s / D s
  have hDan : ∀ s, AnalyticAt ℂ D s := fun s => by fun_prop
  have hRan : ∀ s, D s ≠ 0 → AnalyticAt ℂ R s := fun s hs =>
    (analyticAt_const.mul (hΛQ.analyticAt s)).div (hDan s) hs
  have hRm : MeromorphicOn R Set.univ := fun x _ =>
    (analyticAt_const.mul (hΛQ.analyticAt x)).meromorphicAt.div (hDan x).meromorphicAt
  have hre_ne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h, Complex.zero_re] at hz; linarith
  have hDne : ∀ t : ℂ, 1 < t.re → D t ≠ 0 := by
    intro t ht
    refine mul_ne_zero (hre_ne _ ?_) (hre_ne _ ?_) <;> simp [a] <;> linarith
  have hval : ∀ t : ℂ, 1 < t.re → χ.gammaFactor t * MasulloGRH.heckeEulerProduct χ t = R t := by
    intro t ht
    have hDt := hDne t ht
    rw [hγ]
    simp only [R]
    rw [eq_div_iff hDt, hΛQγ' t (by linarith), eulerProduct_eq, hQP t ht]
    simp only [D, a]
    ring
  have hc1 : ∀ s, D s ≠ 0 → MasulloGRH.completedHeckeLFunction χ s = R s := fun s hs =>
    completed_eq_on χ hex hγm R hRm (fun t ht => ⟨hRan t (hDne t ht), hval t ht⟩) s (hRan s hs)
  have hDne' : ∀ t, t ≠ -a → t ≠ 1 - a → D t ≠ 0 := by
    intro t h1 h2
    refine mul_ne_zero ?_ (sub_ne_zero.2 h2)
    intro h; exact h1 (eq_neg_of_add_eq_zero_left h)
  have hpunct : ∀ p : ℂ, MasulloGRH.completedHeckeLFunction χ =ᶠ[𝓝[≠] p] R := by
    intro p
    by_cases hp1 : p = -a
    · filter_upwards [eventually_ne_punctured p (-a), eventually_ne_punctured p (1 - a)] with t h1 h2
      exact hc1 t (hDne' t h1 h2)
    · filter_upwards [eventually_ne_punctured p (-a), eventually_ne_punctured p (1 - a)] with t h1 h2
      exact hc1 t (hDne' t h1 h2)
  have hp1re : (1 - a).re = 1 := by simp [hare]
  have hΛQp1 : ΛQ (1 - a) ≠ 0 := by
    rw [hΛQγ' (1 - a) (by rw [hp1re]; norm_num)]
    refine mul_ne_zero (by simp only [a]; ring_nf; exact one_ne_zero) (mul_ne_zero
      (tateGamma_ne_zero τ m (by rw [hp1re]; norm_num)) (hQne _ (by rw [hp1re])))
  have hΛQp2 : ΛQ (-a) ≠ 0 := by
    have h1a : (1 + a).re = 1 := by simp [hare]
    have hd : ΛQd (1 + a) ≠ 0 := by
      rw [hΛQdγ' (1 + a) (by rw [h1a]; norm_num)]
      refine mul_ne_zero (by simp only [a]; ring_nf; exact one_ne_zero) (mul_ne_zero
        (tateGamma_ne_zero _ _ (by rw [h1a]; norm_num)) (hQ'ne _ (by rw [h1a])))
    have := hfe (-a)
    rw [sub_neg_eq_add] at this
    rw [this] at hd
    exact right_ne_zero_of_mul hd
  have hgc := gammaConst_ne_zero (F := F)
  refine ⟨fun s hs => (hc1 s (hDne s hs)).trans (hval s hs).symm, ?_, ?_, ?_⟩
  · rw [meromorphicOrderAt_congr (hpunct _)]
    have hfun : R = fun s => (gammaConst F * ΛQ s / (s - (1 - a))) / (s - -a) := by
      funext s; simp only [R, D]; rw [div_div, mul_comm (s - (1 - a)), sub_neg_eq_add]
    rw [hfun]
    refine order_simple_pole _ _ ((analyticAt_const.mul (hΛQ.analyticAt _)).div (by fun_prop) ?_) ?_
    · ring_nf; exact neg_ne_zero.2 one_ne_zero
    · refine div_ne_zero (mul_ne_zero hgc hΛQp2) ?_
      ring_nf; exact neg_ne_zero.2 one_ne_zero
  · rw [meromorphicOrderAt_congr (hpunct _)]
    have hfun : R = fun s => (gammaConst F * ΛQ s / (s + a)) / (s - (1 - a)) := by
      funext s; simp only [R, D]; rw [div_div]
    rw [hfun]
    refine order_simple_pole _ _ ((analyticAt_const.mul (hΛQ.analyticAt _)).div (by fun_prop) ?_) ?_
    · ring_nf; exact one_ne_zero
    · refine div_ne_zero (mul_ne_zero hgc hΛQp1) ?_
      ring_nf; exact one_ne_zero
  · intro s h1 h2
    have hDs := hDne' s h1 h2
    have hopen : IsOpen {t : ℂ | D t ≠ 0} :=
      isOpen_ne_fun (continuous_iff_continuousAt.2 fun t => (hDan t).continuousAt) continuous_const
    have hev : MasulloGRH.completedHeckeLFunction χ =ᶠ[𝓝 s] R := by
      filter_upwards [hopen.mem_nhds hDs] with t ht
      exact hc1 t ht
    refine ⟨(hRan s hDs).congr hev.symm, fun hs => ?_⟩
    rw [hc1 s hDs]
    simp only [R]
    refine div_ne_zero (mul_ne_zero hgc ?_) hDs
    rw [hΛQγ' s (by linarith)]
    refine mul_ne_zero ?_ (mul_ne_zero (tateGamma_ne_zero τ m (by linarith)) (hQne s hs))
    intro h; exact h1 (eq_neg_of_add_eq_zero_left h)


/-- **Proposition 3.2.1.3** for number fields in `Type`. -/
theorem properties (χ : MasulloGRH.HeckeCharacter F) :
    (MeromorphicNFOn (MasulloGRH.completedHeckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → MasulloGRH.completedHeckeLFunction χ s =
        χ.gammaFactor s * MasulloGRH.heckeEulerProduct χ s) ∧
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (MasulloGRH.completedHeckeLFunction χ)) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ →
      meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) (t₀ * Complex.I) = -1 ∧
      meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) (1 + t₀ * Complex.I) = -1 ∧
      ∀ s : ℂ, s ≠ t₀ * Complex.I → s ≠ 1 + t₀ * Complex.I →
        AnalyticAt ℂ (MasulloGRH.completedHeckeLFunction χ) s) ∧
    (∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s : ℂ, ε s ≠ 0) ∧
      ∀ s : ℂ, MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - s) =
        ε s * MasulloGRH.completedHeckeLFunction χ s) ∧
    (∀ s : ℂ, 0 < s.re → 0 < meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) s →
      s.re < 1) := by
  refine ⟨⟨meromorphicNFOn_toMeromorphicNFOn _ _, ?_⟩, ?_, ?_, ?_, ?_⟩
  · by_cases hnp : ∀ τ₀ : ℝ, lift χ ≠ normPowChar F τ₀
    · exact (entire_case χ hnp).1
    · push Not at hnp
      obtain ⟨τ₀, h⟩ := hnp
      exact (normPower_case χ τ₀ h).1
  · intro hnt
    have hnp : ∀ τ₀ : ℝ, lift χ ≠ normPowChar F τ₀ := fun τ₀ h =>
      hnt (isTrivialOnNormOne_of_eq_normPowChar χ τ₀ h)
    exact (entire_case χ hnp).2.1
  · intro t₀ ht₀
    obtain ⟨-, ho1, ho2, han⟩ := normPower_case χ (-t₀) (lift_eq_normPowChar_of_isNormPower χ t₀ ht₀)
    have e1 : -(((-t₀ : ℝ) : ℂ) * Complex.I) = (t₀ : ℂ) * Complex.I := by push_cast; ring
    have e2 : 1 - ((-t₀ : ℝ) : ℂ) * Complex.I = 1 + (t₀ : ℂ) * Complex.I := by push_cast; ring
    rw [e1] at ho1 han
    rw [e2] at ho2 han
    exact ⟨ho1, ho2, fun s h1 h2 => (han s h1 h2).1⟩
  · obtain ⟨ε, Nf, hε, hNf, hfe⟩ := functional_equation χ
    have hNf0 : (Nf : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNf.ne'
    have hε0 : ε ≠ 0 := fun h => by rw [h, norm_zero] at hε; exact zero_ne_one hε
    refine ⟨fun s => ε * (Nf : ℂ) ^ (s - 1 / 2), ?_, fun s => ?_, hfe⟩
    · intro s
      exact (differentiableAt_const _).mul ((differentiableAt_id.sub_const _).const_cpow (Or.inl hNf0))
    · refine mul_ne_zero hε0 ?_
      rw [Complex.cpow_def_of_ne_zero hNf0]; exact Complex.exp_ne_zero _
  · intro s hs hord
    by_contra hre
    push Not at hre
    by_cases hnp : ∀ τ₀ : ℝ, lift χ ≠ normPowChar F τ₀
    · obtain ⟨-, hdiff, hne⟩ := entire_case χ hnp
      rw [order_zero_of_analytic (hdiff.analyticAt s) (hne s hre)] at hord
      exact lt_irrefl _ hord
    · push Not at hnp
      obtain ⟨τ₀, h⟩ := hnp
      obtain ⟨-, -, ho2, han⟩ := normPower_case χ τ₀ h
      by_cases hs1 : s = 1 - ((τ₀ : ℝ) : ℂ) * Complex.I
      · rw [hs1, ho2] at hord
        exact absurd hord (by decide)
      · have hs2 : s ≠ -(((τ₀ : ℝ) : ℂ) * Complex.I) := by
          intro h2; rw [h2] at hre; simp at hre; linarith
        obtain ⟨han', hne⟩ := han s hs2 hs1
        rw [order_zero_of_analytic han' (hne hre)] at hord
        exact lt_irrefl _ hord

end MasulloTateBridge

end

end

theorem solution
    (F : Type) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) :
    (MeromorphicNFOn (MasulloGRH.completedHeckeLFunction χ) Set.univ ∧
      ∀ s : ℂ, 1 < s.re → MasulloGRH.completedHeckeLFunction χ s =
        χ.gammaFactor s * MasulloGRH.heckeEulerProduct χ s) ∧
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (MasulloGRH.completedHeckeLFunction χ)) ∧
    (∀ t₀ : ℝ, χ.IsNormPower t₀ →
      meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) (t₀ * Complex.I) = -1 ∧
      meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) (1 + t₀ * Complex.I) = -1 ∧
      ∀ s : ℂ, s ≠ t₀ * Complex.I → s ≠ 1 + t₀ * Complex.I →
        AnalyticAt ℂ (MasulloGRH.completedHeckeLFunction χ) s) ∧
    (∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s : ℂ, ε s ≠ 0) ∧
      ∀ s : ℂ, MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - s) =
        ε s * MasulloGRH.completedHeckeLFunction χ s) ∧
    (∀ s : ℂ, 0 < s.re → 0 < meromorphicOrderAt (MasulloGRH.completedHeckeLFunction χ) s →
      s.re < 1) :=
  MasulloTateBridge.properties χ
