-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_functional_equation_explicit_univ
-- status  : ACCEPTED   (prove)
-- author  : @flashonfire
-- created : 2026-11-21T20:47:22.146374+00:00
-- url     : https://prove2.me/submissions/5fbf4599-20d9-45de-9a5b-0fa16137a1fc

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.UniformRing
import Mathlib

universe u v

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

-- Transport infrastructure adapted from the accepted proof of
-- `MasulloGRH.exists_tate_hecke_character_preserving_local_prime_values` (Apache 2.0).

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped Topology
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open UniformSpace Filter
open scoped Topology WithZero
noncomputable section
namespace TatePrimeTransport
variable {F : Type u} {K : Type v} [Field F] [Field K] [NumberField F] [NumberField K]

abbrev primeEquiv (r : F ≃+* K) := equivOfRingEquiv (RingOfIntegers.mapRingEquiv r)

theorem intVal (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    (primeEquiv r p).intValuation (RingOfIntegers.mapRingEquiv r x) = p.intValuation x := by
  let e := RingOfIntegers.mapRingEquiv r
  let E : Ideal (𝓞 F) ≃* Ideal (𝓞 K) :=
    { e.idealComapOrderIso.symm.toEquiv with map_mul' := Ideal.map_mul e }
  by_cases hx : x = 0
  · simp [hx]
  have hp : (primeEquiv r p).asIdeal = E p.asIdeal := Ideal.comap_symm e
  have hs : Ideal.span {e x} = E (Ideal.span {x}) := by
    change _ = Ideal.map e _
    rw [Ideal.map_span, Set.image_singleton]
  change (primeEquiv r p).intValuation (e x) = _
  rw [intValuation_eq_exp_neg_multiplicity _ (by simpa using hx),
    intValuation_eq_exp_neg_multiplicity _ hx, hp, hs, multiplicity_map_eq E]

theorem fieldVal (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : F) :
    (primeEquiv r p).valuation K (r x) = p.valuation F x := by
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have he (c : 𝓞 F) : r (algebraMap (𝓞 F) F c) =
      algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv r c) := rfl
  simp only [map_div₀, he, valuation_of_algebraMap, intVal]

theorem uc {A B : Type*} [Field A] [Field B] [Valued A ℤᵐ⁰] [Valued B ℤᵐ⁰]
    (r : A ≃+* B) (hv : ∀ x, Valued.v (r x) = (Valued.v x : ℤᵐ⁰)) :
    UniformContinuous r := by
  refine uniformContinuous_of_continuousAt_zero r ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨b, hb⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (.ofClass (Valued.v : Valuation B ℤᵐ⁰)) (γ : _)
  change (Valued.v : Valuation B ℤᵐ⁰).restrict b = γ.val at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hb.symm)
  refine ⟨Units.mk0 ((Valued.v : Valuation A ℤᵐ⁰).restrict (r.symm b)) (by simp [hb0]), ?_⟩
  intro x hx
  change (Valued.v : Valuation B ℤᵐ⁰).restrict (r x) < γ.val
  rw [← hb, Valuation.restrict_lt_iff, hv, ← r.apply_symm_apply b, hv]
  exact ((Valued.v : Valuation A ℤᵐ⁰).restrict_lt_iff).mp hx

abbrev wr (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :=
  WithVal.congr (p.valuation F) ((primeEquiv r p).valuation K) r

theorem wr_uc (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    UniformContinuous (wr r p) := uc _ (fun x => fieldVal r p x.ofVal)

theorem wr_uc_inv (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    UniformContinuous (wr r p).symm := uc _ (fun x => by
  change p.valuation F (r.symm x.ofVal) = (primeEquiv r p).valuation K x.ofVal
  simpa using (fieldVal r p (r.symm x.ofVal)).symm)

def localEquiv (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    p.adicCompletion F ≃+* (primeEquiv r p).adicCompletion K :=
  (adicCompletion.equiv F p).trans <|
    (Completion.mapRingEquiv (wr r p) (wr_uc r p).continuous
      (wr_uc_inv r p).continuous).trans (adicCompletion.equiv K (primeEquiv r p)).symm

theorem localEquiv_continuous (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    Continuous (localEquiv r p) :=
  (adicCompletion.continuous_ofCompletion K _).comp
    (Completion.continuous_map.comp (adicCompletion.continuous_toCompletion F p))

theorem localEquiv_symm_continuous (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    Continuous (localEquiv r p).symm :=
  (adicCompletion.continuous_ofCompletion F _).comp
    (Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K _))

theorem localEquiv_coe (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : F) :
    localEquiv r p (algebraMap F _ x) = algebraMap K _ (r x) := by
  apply adicCompletion.ext
  change Completion.map (wr r p) ((WithVal.toVal (p.valuation F) x : WithVal _) : Completion _) = _
  rw [Completion.map_coe (wr_uc r p)]
  rfl

open WithZeroTopology in
theorem localEquiv_valuation (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    Valued.v (localEquiv r p x) = (Valued.v x : ℤᵐ⁰) := by
  let q := primeEquiv r p
  have hF := Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective F p)
  have hK := Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K q)
  refine (denseRange_algebraMap F p).induction_on (p := fun y => Valued.v (localEquiv r p y) = (Valued.v y : ℤᵐ⁰)) x (isClosed_eq (hK.comp (localEquiv_continuous r p)) hF) ?_
  intro a
  rw [localEquiv_coe]
  exact (adicCompletion.valued_coe K q (r a)).trans
    ((fieldVal r p a).trans (adicCompletion.valued_coe F p a).symm)

end TatePrimeTransport

namespace TatePrimeTransport
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

theorem finitePull_local_mem (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Set.MapsTo (localEquiv r v).symm
      ((primeEquiv r v).adicCompletionIntegers K : Set _)
      (v.adicCompletionIntegers F : Set _) := by
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  simpa only [RingEquiv.apply_symm_apply] using
    (localEquiv_valuation r v ((localEquiv r v).symm x)).symm.le.trans
      (by simpa only [RingEquiv.apply_symm_apply] using hx)

def finitePull (r : F ≃+* K) :
    FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (primeEquiv r)
    (primeEquiv r).injective.tendsto_cofinite (fun v => (localEquiv r v).symm.toRingHom)
    (Eventually.of_forall (finitePull_local_mem r))

theorem finitePull_continuous (r : F ≃+* K) : Continuous (finitePull r) := by
  apply RestrictedProduct.mapAlong_continuous _ _ (primeEquiv r) (primeEquiv r).injective.tendsto_cofinite
    (fun v => (localEquiv r v).symm) (Eventually.of_forall (finitePull_local_mem r))
  exact localEquiv_symm_continuous r

theorem finitePull_diagonal (r : F ≃+* K) (z : K) :
    finitePull r (algebraMap K _ z) = algebraMap F _ (r.symm z) := by
  apply Subtype.ext
  funext v
  change (localEquiv r v).symm (algebraMap K _ z) = algebraMap F _ (r.symm z)
  apply (localEquiv r v).injective
  rw [RingEquiv.apply_symm_apply, localEquiv_coe, RingEquiv.apply_symm_apply]

theorem finitePull_single (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F))
    (u : ((primeEquiv r v).adicCompletion K)ˣ) :
    Units.map (finitePull r).toMonoidHom (MasulloGRH.finiteIdeleSingle (primeEquiv r v) u) =
      MasulloGRH.finiteIdeleSingle v (Units.map (localEquiv r v).symm.toMonoidHom u) := by
  classical
  apply Units.ext
  apply Subtype.ext
  funext w
  change (localEquiv r w).symm
    ((RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 K) => (Submonoid.ofClass (v.adicCompletionIntegers K)).units) (primeEquiv r v) u (primeEquiv r w) : ((primeEquiv r w).adicCompletion K)ˣ) : _) =
      ((RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 F) => (Submonoid.ofClass (v.adicCompletionIntegers F)).units) v (Units.map (localEquiv r v).symm.toMonoidHom u) w : (w.adicCompletion F)ˣ) : _)
  by_cases hw : w = v
  · subst w
    rw [RestrictedProduct.mulSingle_eq_same, RestrictedProduct.mulSingle_eq_same]
    rfl
  · have he := (primeEquiv r).injective.ne hw
    rw [RestrictedProduct.mulSingle_eq_of_ne _ _ he, RestrictedProduct.mulSingle_eq_of_ne _ _ hw]
    exact map_one _

end
end TatePrimeTransport

open NumberField IsDedekindDomain TatePrimeTransport

noncomputable def phase_local_unit_pull {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    ((primeEquiv r v).adicCompletion K)ˣ ≃* (v.adicCompletion F)ˣ :=
  Units.mapEquiv (localEquiv r v).symm.toMulEquiv

theorem phase_local_unit_pull_valuation {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F))
    (x : ((primeEquiv r v).adicCompletion K)ˣ) :
    Valued.v (phase_local_unit_pull r v x : v.adicCompletion F) =
      (Valued.v (x : (primeEquiv r v).adicCompletion K) : ℤᵐ⁰) := by
  change Valued.v ((localEquiv r v).symm x) = _
  simpa only [RingEquiv.apply_symm_apply] using
    (localEquiv_valuation r v ((localEquiv r v).symm x)).symm


open NumberField
open scoped Topology
noncomputable section

def phase_abs_hom {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : WithAbs (w.comap r).1 →+* WithAbs w.1 :=
  (WithAbs.equiv w.1).symm.toRingHom.comp (r.comp (WithAbs.equiv (w.comap r).1).toRingHom)

theorem phase_abs_isometry {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : Isometry (phase_abs_hom r w) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  exact (InfinitePlace.comap_apply w r _).symm

def phase_arch_local {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : (w.comap r).Completion →+* w.Completion :=
  (InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (phase_abs_hom r w) (phase_abs_isometry r w).continuous).comp
      (InfinitePlace.Completion.equiv (w.comap r)).toRingHom)

theorem phase_arch_local_cont {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : Continuous (phase_arch_local r w) :=
  (InfinitePlace.Completion.continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp
      (InfinitePlace.Completion.continuous_toCompletion (w.comap r)))

theorem phase_arch_local_diag {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) (x : F) :
    phase_arch_local r w (algebraMap F (w.comap r).Completion x) = algebraMap K w.Completion (r x) := by
  apply InfinitePlace.Completion.ext
  change (UniformSpace.Completion.mapRingHom (phase_abs_hom r w) (phase_abs_isometry r w).continuous
    (↑((WithAbs.equiv (w.comap r).1).symm x) : (w.comap r).1.Completion)) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

def phase_arch_hom {F K : Type*} [Field F] [Field K] (r : F →+* K) :
    InfiniteAdeleRing F →+* InfiniteAdeleRing K where
  toFun x w := phase_arch_local r w (x (w.comap r))
  map_zero' := by funext w; exact map_zero _
  map_one' := by funext w; exact map_one _
  map_mul' x y := by funext w; exact map_mul _ _ _
  map_add' x y := by funext w; exact map_add _ _ _

theorem phase_arch_continuous {F K : Type*} [Field F] [Field K] (r : F →+* K) :
    Continuous (phase_arch_hom r) :=
  continuous_pi (fun w => (phase_arch_local_cont r w).comp (continuous_apply (w.comap r)))

theorem phase_arch_diagonal {F K : Type*} [Field F] [Field K] (r : F →+* K) (x : F) :
    phase_arch_hom r (algebraMap F (InfiniteAdeleRing F) x) =
      algebraMap K (InfiniteAdeleRing K) (r x) := by
  funext w
  exact phase_arch_local_diag r w x


open NumberField IsDedekindDomain

theorem phase_make_global_pull
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K))
    (l : ∀ v : HeightOneSpectrum (𝓞 F), ((e v).adicCompletion K)ˣ →* (v.adicCompletion F)ˣ)
    (A : InfiniteAdeleRing K →+* InfiniteAdeleRing F)
    (B : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 F) F)
    (hA : Continuous A) (hB : Continuous B)
    (da : ∀ x : K, A (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap F (InfiniteAdeleRing F) (r.symm x))
    (db : ∀ x : K, B (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (r.symm x))
    (bs : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ((e v).adicCompletion K)ˣ),
      Units.map B.toMonoidHom (MasulloGRH.finiteIdeleSingle (e v) x) =
        MasulloGRH.finiteIdeleSingle v (l v x)) :
    ∃ M : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 F) F)ˣ,
      Continuous M ∧
      (∀ u : Kˣ, M (MasulloGRH.principalIdele K u) =
        MasulloGRH.principalIdele F (Units.map r.symm.toMonoidHom u)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ((e v).adicCompletion K)ˣ),
        M (MasulloGRH.ideleSingle (e v) x) = MasulloGRH.ideleSingle v (l v x) := by
  let H : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F := A.prodMap B
  have hc : Continuous H := (hA.comp continuous_fst).prodMk (hB.comp continuous_snd)
  refine ⟨Units.map H.toMonoidHom, Continuous.units_map _ hc, ?_, ?_⟩
  · intro u
    apply Units.ext
    exact Prod.ext (da u) (db u)
  · intro v x
    apply Units.ext
    refine Prod.ext ?_ ?_
    · exact map_one A
    · exact congrArg Units.val (bs v x)

open NumberField IsDedekindDomain NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

theorem phase_single_eq {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    MasulloGRH.ideleSingle v x = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v x) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · rfl
  refine Subtype.ext (funext fun w => ?_)
  change ((RestrictedProduct.mulSingle
    (fun v : HeightOneSpectrum (𝓞 K) => (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
      v x w : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
    ((localUnit (𝓞 K) K v x : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w
  by_cases h : w = v
  · subst w
    rw [RestrictedProduct.mulSingle_eq_same, localUnit_apply_self]
  · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, localUnit_apply_of_ne _ _ _ _ h]
    rfl



/-! ### Archimedean local maps: embeddings, isometry, bijectivity -/

section ArchLocal

open NumberField NumberField.InfinitePlace ComplexConjugate

variable {k K' : Type*} [Field k] [Field K']

theorem arch_local_coe (f : k →+* K') (w : InfinitePlace K') (x : WithAbs (w.comap f).1) :
    phase_arch_local f w (x : (w.comap f).Completion) =
      ((phase_abs_hom f w x : WithAbs w.1) : w.Completion) := by
  apply InfinitePlace.Completion.ext
  change (UniformSpace.Completion.mapRingHom (phase_abs_hom f w) (phase_abs_isometry f w).continuous
    (↑x : (w.comap f).1.Completion)) = _
  rw [UniformSpace.Completion.mapRingHom_coe]

theorem norm_ext (w : InfinitePlace K') (y : w.Completion) :
    ‖Completion.extensionEmbedding w y‖ = ‖y‖ :=
  (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y

theorem arch_local_emb (f : k →+* K') (w : InfinitePlace K') :
    (∀ y, Completion.extensionEmbedding w (phase_arch_local f w y) =
        Completion.extensionEmbedding (w.comap f) y) ∨
    (∀ y, Completion.extensionEmbedding w (phase_arch_local f w y) =
        conj (Completion.extensionEmbedding (w.comap f) y)) := by
  have hc : w.comap f = InfinitePlace.mk (w.embedding.comp f) := by
    rw [← comap_mk, mk_embedding]
  have hcont1 : Continuous fun y => Completion.extensionEmbedding w (phase_arch_local f w y) :=
    (Completion.isometry_extensionEmbedding w).continuous.comp (phase_arch_local_cont f w)
  have hcont2 : Continuous fun y : (w.comap f).Completion => Completion.extensionEmbedding (w.comap f) y :=
    (Completion.isometry_extensionEmbedding _).continuous
  rcases embedding_mk_eq (w.embedding.comp f) with h | h
  · left
    intro y
    induction y using InfinitePlace.Completion.induction_on with
    | hp => exact isClosed_eq hcont1 hcont2
    | ih x =>
      rw [arch_local_coe, Completion.extensionEmbedding_coe, Completion.extensionEmbedding_coe]
      have he : (w.comap f).embedding = w.embedding.comp f := by rw [hc, h]
      rw [he]; rfl
  · right
    intro y
    induction y using InfinitePlace.Completion.induction_on with
    | hp => exact isClosed_eq hcont1 (Complex.continuous_conj.comp hcont2)
    | ih x =>
      rw [arch_local_coe, Completion.extensionEmbedding_coe, Completion.extensionEmbedding_coe]
      have he : (w.comap f).embedding = ComplexEmbedding.conjugate (w.embedding.comp f) := by
        rw [hc, h]
      rw [he]
      change _ = conj (conj (w.embedding (f _)))
      rw [Complex.conj_conj]; rfl

theorem arch_local_norm (f : k →+* K') (w : InfinitePlace K') (y : (w.comap f).Completion) :
    ‖phase_arch_local f w y‖ = ‖y‖ := by
  rw [← norm_ext, ← norm_ext (w.comap f)]
  rcases arch_local_emb f w with h | h
  · rw [h]
  · rw [h, Complex.norm_conj]

theorem arch_local_bijective (f : k ≃+* K') (w : InfinitePlace K') :
    Function.Bijective (phase_arch_local (f : k →+* K') w) := by
  refine ⟨(phase_arch_local (f : k →+* K') w).injective, ?_⟩
  have hiso : Isometry (phase_arch_local (f : k →+* K') w) :=
    AddMonoidHomClass.isometry_of_norm _ (arch_local_norm _ w)
  have hclosed : IsClosed (Set.range (phase_arch_local (f : k →+* K') w)) :=
    hiso.isClosedEmbedding.isClosed_range
  have hdense : Dense (Set.range (phase_arch_local (f : k →+* K') w)) := by
    refine (InfinitePlace.Completion.denseRange_coe (v := w)).mono ?_
    rintro _ ⟨y, rfl⟩
    refine ⟨((WithAbs.equiv (w.comap (f : k →+* K')).1).symm (f.symm (WithAbs.equiv w.1 y)) :
      WithAbs (w.comap (f : k →+* K')).1), ?_⟩
    rw [arch_local_coe]
    refine congrArg (fun t : WithAbs w.1 => (t : w.Completion)) ?_
    change (WithAbs.equiv w.1).symm (f ((WithAbs.equiv (w.comap (f : k →+* K')).1)
      ((WithAbs.equiv (w.comap (f : k →+* K')).1).symm (f.symm (WithAbs.equiv w.1 y))))) = y
    simp
  intro z
  have : z ∈ Set.range (phase_arch_local (f : k →+* K') w) := by
    rw [← hclosed.closure_eq, hdense.closure_eq]; exact Set.mem_univ z
  exact this

end ArchLocal

/-! ### The adelic pullback and its bijectivity -/

section Pull

open NumberField NumberField.InfinitePlace IsDedekindDomain TatePrimeTransport

variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

/-- The bijection of infinite places `w ↦ w ∘ r⁻¹`. -/
def placeEquiv (r : F ≃+* K) : InfinitePlace F ≃ InfinitePlace K where
  toFun w := w.comap (r.symm : K →+* F)
  invFun u := u.comap (r : F →+* K)
  left_inv w := by
    show (w.comap (r.symm : K →+* F)).comap (r : F →+* K) = w
    rw [← comap_comp]
    have : (r.symm : K →+* F).comp (r : F →+* K) = RingHom.id F := by ext; simp
    rw [this, InfinitePlace.comap_id]
  right_inv u := by
    show (u.comap (r : F →+* K)).comap (r.symm : K →+* F) = u
    rw [← comap_comp]
    have : (r : F →+* K).comp (r.symm : K →+* F) = RingHom.id K := by ext; simp
    rw [this, InfinitePlace.comap_id]

/-- The adelic pullback `𝔸_K → 𝔸_F`. -/
def pullHom (r : F ≃+* K) : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F :=
  (phase_arch_hom (r.symm : K →+* F)).prodMap (finitePull r)

theorem pullHom_continuous (r : F ≃+* K) : Continuous (pullHom r) :=
  ((phase_arch_continuous _).comp continuous_fst).prodMk ((finitePull_continuous r).comp continuous_snd)

theorem phase_arch_hom_bijective (r : F ≃+* K) :
    Function.Bijective (phase_arch_hom (r.symm : K →+* F)) := by
  set σ := placeEquiv r
  have hφ : ∀ w : InfinitePlace F, Function.Bijective (phase_arch_local (r.symm : K →+* F) w) :=
    fun w => arch_local_bijective r.symm w
  constructor
  · intro x y hxy
    funext u
    obtain ⟨w, rfl⟩ := σ.surjective u
    have := congrFun hxy w
    exact (hφ w).1 this
  · intro z
    let f : ∀ w : InfinitePlace F, w.Completion ≃ (σ w).Completion := fun w =>
      (Equiv.ofBijective _ (hφ w)).symm
    refine ⟨Equiv.piCongr σ f z, ?_⟩
    funext w
    change phase_arch_local (r.symm : K →+* F) w (Equiv.piCongr σ f z (σ w)) = z w
    rw [Equiv.piCongr_apply_apply]
    exact (Equiv.ofBijective _ (hφ w)).apply_symm_apply (z w)

theorem finitePull_bijective (r : F ≃+* K) : Function.Bijective (finitePull r) := by
  set e := primeEquiv r
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext u
    obtain ⟨v, rfl⟩ := e.surjective u
    have h := congrArg (fun t : FiniteAdeleRing (𝓞 F) F => t v) hxy
    exact (localEquiv r v).symm.injective h
  · intro z
    let y₀ : ∀ u : HeightOneSpectrum (𝓞 K), u.adicCompletion K :=
      Equiv.piCongr e (fun v => (localEquiv r v).toEquiv) (fun v => z v)
    have hy₀ : ∀ v, y₀ (e v) = localEquiv r v (z v) := fun v =>
      Equiv.piCongr_apply_apply e (fun v => (localEquiv r v).toEquiv) (fun v => z v) v
    have hint : ∀ᶠ u in Filter.cofinite, y₀ u ∈ u.adicCompletionIntegers K := by
      have hz : ∀ᶠ u in Filter.cofinite, z (e.symm u) ∈ (e.symm u).adicCompletionIntegers F :=
        e.symm.injective.tendsto_cofinite.eventually z.2
      refine hz.mono fun u hu => ?_
      obtain ⟨v, rfl⟩ := e.surjective u
      rw [e.symm_apply_apply] at hu
      rw [hy₀, HeightOneSpectrum.mem_adicCompletionIntegers, localEquiv_valuation]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hu
    refine ⟨⟨y₀, hint⟩, ?_⟩
    apply Subtype.ext
    funext v
    change (localEquiv r v).symm (y₀ (e v)) = z v
    rw [hy₀, RingEquiv.symm_apply_apply]

theorem pullHom_bijective (r : F ≃+* K) : Function.Bijective (pullHom r) :=
  ⟨fun x y h => Prod.ext ((phase_arch_hom_bijective r).1 (congrArg Prod.fst h))
      ((finitePull_bijective r).1 (congrArg Prod.snd h)),
    fun z => by
      obtain ⟨a, ha⟩ := (phase_arch_hom_bijective r).2 z.1
      obtain ⟨b, hb⟩ := (finitePull_bijective r).2 z.2
      exact ⟨(a, b), Prod.ext ha hb⟩⟩

/-- The pullback of ideles, a group isomorphism `𝔸_K^× ≃ 𝔸_F^×`. -/
def pullIdele (r : F ≃+* K) : MasulloGRH.IdeleGroup K ≃* MasulloGRH.IdeleGroup F :=
  Units.mapEquiv (RingEquiv.ofBijective (pullHom r) (pullHom_bijective r)).toMulEquiv

theorem pullIdele_val (r : F ≃+* K) (g : MasulloGRH.IdeleGroup K) :
    ((pullIdele r g : MasulloGRH.IdeleGroup F) : AdeleRing (𝓞 F) F) = pullHom r g := rfl

theorem pullIdele_continuous (r : F ≃+* K) : Continuous (pullIdele r) :=
  Continuous.units_map _ (pullHom_continuous r)

theorem pullIdele_principal (r : F ≃+* K) (u : Kˣ) :
    pullIdele r (MasulloGRH.principalIdele K u) =
      MasulloGRH.principalIdele F (Units.map r.symm.toMonoidHom u) := by
  apply Units.ext
  exact Prod.ext (phase_arch_diagonal (r.symm : K →+* F) (u : K)) (finitePull_diagonal r (u : K))

end Pull

/-! ### Transport of Hecke characters and of their Euler products -/

section CharTransport

open NumberField IsDedekindDomain TatePrimeTransport MasulloGRH

variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

local notation "AF" => AdeleRing (𝓞 F) F

-- coordinates of `ideleSingle` (as in the accepted continuation proof)
open Classical in
theorem ideleSingle_fin_self' (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    (ideleSingle v x : AF).2 v = x := by
  change ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletion F)ˣ) v x v :
    (v.adicCompletion F)ˣ) : v.adicCompletion F) = x
  rw [Pi.mulSingle_eq_same]

open Classical in
theorem ideleSingle_fin_ne' (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) : (ideleSingle v x : AF).2 w = 1 := by
  change ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletion F)ˣ) v x w :
    (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1
  rw [Pi.mulSingle_eq_of_ne h, Units.val_one]

theorem ideleSingle_mul' (v : HeightOneSpectrum (𝓞 F)) (x y : (v.adicCompletion F)ˣ) :
    ideleSingle v (x * y) = ideleSingle v x * ideleSingle v y := by
  apply Units.ext
  apply Prod.ext
  · show (1 : InfiniteAdeleRing F) = 1 * 1
    rw [one_mul]
  · apply RestrictedProduct.ext; intro w
    show (ideleSingle v (x * y) : AF).2 w = (ideleSingle v x : AF).2 w * (ideleSingle v y : AF).2 w
    by_cases h : w = v
    · subst h; rw [ideleSingle_fin_self', ideleSingle_fin_self', ideleSingle_fin_self', Units.val_mul]
    · rw [ideleSingle_fin_ne' _ _ _ h, ideleSingle_fin_ne' _ _ _ h, ideleSingle_fin_ne' _ _ _ h,
        one_mul]

theorem localComponent_mul (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x y : (v.adicCompletion F)ˣ) :
    χ.localComponent v (x * y) = χ.localComponent v x * χ.localComponent v y := by
  unfold HeckeCharacter.localComponent
  rw [ideleSingle_mul', QuotientGroup.mk_mul, map_mul, Circle.coe_mul]

/-- `primeValue` may be computed at any uniformizer. -/
theorem primeValue_eq_of_uniformizer (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hu : χ.IsUnramifiedAt v) (π : (v.adicCompletion F)ˣ) (hπ : IsUniformizerAt v π) :
    χ.primeValue v = χ.localComponent v π := by
  unfold HeckeCharacter.primeValue
  have hex : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x := ⟨hu, π, hπ⟩
  rw [dif_pos hex]
  set y := hex.2.choose
  have hy : IsUniformizerAt v y := hex.2.choose_spec
  have h1 : χ.localComponent v (y * π⁻¹) = 1 := by
    apply hu
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    unfold IsUniformizerAt at hy hπ
    rw [hy, hπ, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have := localComponent_mul χ v (y * π⁻¹) π
  rw [inv_mul_cancel_right, h1, one_mul] at this
  exact this

/-- The map of idele class groups induced by the pullback. -/
def classMap (r : F ≃+* K) : IdeleClassGroup K →* IdeleClassGroup F :=
  QuotientGroup.map (principalIdeles K) (principalIdeles F) (pullIdele r).toMonoidHom (by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map r.symm.toMonoidHom u, (pullIdele_principal r u).symm⟩)

theorem classMap_mk (r : F ≃+* K) (g : IdeleGroup K) :
    classMap r (QuotientGroup.mk g) = QuotientGroup.mk (pullIdele r g) := rfl

theorem classMap_continuous (r : F ≃+* K) : Continuous (classMap r) :=
  continuous_quot_lift _ (QuotientGroup.continuous_mk.comp (pullIdele_continuous r))

/-- The transported Hecke character `χ ∘ (pullback)` of `K`. -/
def transport (r : F ≃+* K) (χ : HeckeCharacter F) : HeckeCharacter K :=
  ⟨χ.toMonoidHom.comp (classMap r), χ.continuous.comp (classMap_continuous r)⟩

theorem transport_apply (r : F ≃+* K) (χ : HeckeCharacter F) (g : IdeleGroup K) :
    transport r χ (QuotientGroup.mk g) = χ (QuotientGroup.mk (pullIdele r g)) := rfl

theorem transport_inv (r : F ≃+* K) (χ : HeckeCharacter F) :
    transport r χ⁻¹ = (transport r χ)⁻¹ := by
  ext x; rfl

theorem pullIdele_single (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F))
    (x : ((primeEquiv r v).adicCompletion K)ˣ) :
    pullIdele r (ideleSingle (primeEquiv r v) x) = ideleSingle v (phase_local_unit_pull r v x) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · show phase_arch_hom (r.symm : K →+* F) 1 = 1
    exact map_one _
  · exact congrArg Units.val (finitePull_single r v x)

theorem localComponent_transport (r : F ≃+* K) (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (x : ((primeEquiv r v).adicCompletion K)ˣ) :
    (transport r χ).localComponent (primeEquiv r v) x = χ.localComponent v (phase_local_unit_pull r v x) := by
  unfold HeckeCharacter.localComponent
  rw [transport_apply, pullIdele_single]

theorem unram_transport_iff (r : F ≃+* K) (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (transport r χ).IsUnramifiedAt (primeEquiv r v) ↔ χ.IsUnramifiedAt v := by
  constructor
  · intro h x hx
    set y := (phase_local_unit_pull r v).symm x
    have hy : phase_local_unit_pull r v y = x := (phase_local_unit_pull r v).apply_symm_apply x
    rw [← hy, ← localComponent_transport]
    apply h
    rw [← phase_local_unit_pull_valuation, hy]; exact hx
  · intro h x hx
    rw [localComponent_transport]
    apply h
    rw [phase_local_unit_pull_valuation]; exact hx

theorem primeValue_transport (r : F ≃+* K) (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (transport r χ).primeValue (primeEquiv r v) = χ.primeValue v := by
  by_cases hu : χ.IsUnramifiedAt v
  · have hu' := (unram_transport_iff r χ v).2 hu
    set π := NumberField.AdelicLevel.uniformizerUnit K (primeEquiv r v)
    have hπ : IsUniformizerAt (primeEquiv r v) π := NumberField.AdelicLevel.valued_uniformizerUnit K _
    rw [primeValue_eq_of_uniformizer _ _ hu' π hπ, localComponent_transport,
      primeValue_eq_of_uniformizer χ v hu (phase_local_unit_pull r v π)]
    unfold IsUniformizerAt
    rw [phase_local_unit_pull_valuation]; exact hπ
  · have hu' : ¬ (transport r χ).IsUnramifiedAt (primeEquiv r v) := fun h => hu ((unram_transport_iff r χ v).1 h)
    unfold HeckeCharacter.primeValue
    rw [dif_neg (fun h => hu' h.1), dif_neg (fun h => hu h.1)]

theorem absNorm_primeEquiv (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (primeEquiv r v).asIdeal = Ideal.absNorm v.asIdeal := by
  set e := RingOfIntegers.mapRingEquiv r
  have hJ : (primeEquiv r v).asIdeal = Ideal.map e v.asIdeal := by
    exact Ideal.comap_symm e
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply,
    hJ]
  exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal (Ideal.map e v.asIdeal) e rfl).toEquiv.symm

theorem eulerProduct_transport (r : F ≃+* K) (χ : HeckeCharacter F) :
    heckeEulerProduct (transport r χ) = heckeEulerProduct χ := by
  funext s
  unfold heckeEulerProduct
  rw [← (primeEquiv r).tprod_eq]
  congr 1
  funext v
  rw [primeValue_transport, absNorm_primeEquiv]

theorem heckeLFunction_transport (r : F ≃+* K) (χ : HeckeCharacter F) :
    heckeLFunction (transport r χ) = heckeLFunction χ := by
  unfold heckeLFunction
  rw [eulerProduct_transport]

end CharTransport

/-! ### Universe-polymorphic uniqueness lemmas (copied from the Type-0 bridge) -/

section UniqG

open NumberField

variable {F : Type*} [Field F] [NumberField F]

theorem norm_extensionEmbeddingG (w : InfinitePlace F) (y : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w y‖ = ‖y‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y

/-- Every positive real is the image of a unit of `F_w`. -/
theorem exists_unit_realG (w : InfinitePlace F) (c : ℝ) (hc : 0 < c) :
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

theorem cpow_ofReal_exp_mul_IG (θ t : ℝ) :
    ((Real.exp θ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) = Complex.exp ((t * θ : ℝ) * Complex.I) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  congr 1
  push_cast
  ring


theorem exp_pi_I_ne_oneG : Complex.exp ((Real.pi : ℂ) * Complex.I) ≠ 1 := by
  rw [Complex.exp_pi_mul_I]; norm_num

/-- Uniqueness of the archimedean exponent. -/
theorem exponent_uniqueG (w : InfinitePlace F) (f : (w.Completion)ˣ → ℂ) (t t' : ℝ)
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
  obtain ⟨x, hx⟩ := exists_unit_realG w (Real.exp (θ / w.mult)) (Real.exp_pos _)
  have hnorm : ‖(x : w.Completion)‖ ^ w.mult = Real.exp θ := by
    rw [← norm_extensionEmbeddingG, hx, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← Real.exp_nat_mul, mul_div_cancel₀ _ hm0]
  have h1 := ht x (by rw [hx, Complex.ofReal_im]) (by rw [hx, Complex.ofReal_re]; exact Real.exp_pos _)
  have h2 := ht' x (by rw [hx, Complex.ofReal_im]) (by rw [hx, Complex.ofReal_re]; exact Real.exp_pos _)
  rw [hnorm, cpow_ofReal_exp_mul_IG] at h1 h2
  have h3 : Complex.exp ((t * θ : ℝ) * Complex.I) = Complex.exp ((t' * θ : ℝ) * Complex.I) :=
    h1.symm.trans h2
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
    have hpi : ((t * θ : ℝ) : ℂ) * Complex.I - ((t' * θ : ℝ) : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I := by
      have : (t - t') * θ = Real.pi := by simp only [θ]; field_simp
      rw [← sub_mul, ← Complex.ofReal_sub, ← sub_mul, this]
    rw [← hpi, Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]
  exact exp_pi_I_ne_oneG h4

/-- Uniqueness of the archimedean weight at a complex place. -/
theorem weight_uniqueG (w : InfinitePlace F) (hw : w.IsComplex) (f : (w.Completion)ˣ → ℂ) (n n' : ℤ)
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
    rw [← norm_extensionEmbeddingG]; change ‖InfinitePlace.Completion.extensionEmbedding w y‖ = 1
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
  exact exp_pi_I_ne_oneG h4



end UniqG

/-! ### Transport of the archimedean data and of `Γ_F` -/

section ArchTransport

open NumberField NumberField.InfinitePlace IsDedekindDomain TatePrimeTransport MasulloGRH ComplexConjugate

variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

/-- The local isomorphism `K_{σ w} ≃ F_w`. -/
def archEquiv (r : F ≃+* K) (w : InfinitePlace F) :
    (placeEquiv r w).Completion ≃+* w.Completion :=
  RingEquiv.ofBijective (phase_arch_local (r.symm : K →+* F) w) (arch_local_bijective r.symm w)

/-- On units. -/
def archUnitsEquiv (r : F ≃+* K) (w : InfinitePlace F) :
    ((placeEquiv r w).Completion)ˣ ≃* (w.Completion)ˣ :=
  Units.mapEquiv (archEquiv r w).toMulEquiv

theorem archUnitsEquiv_val (r : F ≃+* K) (w : InfinitePlace F) (y : ((placeEquiv r w).Completion)ˣ) :
    ((archUnitsEquiv r w y : (w.Completion)ˣ) : w.Completion) =
      phase_arch_local (r.symm : K →+* F) w (y : (placeEquiv r w).Completion) := rfl

theorem pullIdele_singleInfinite (r : F ≃+* K) (w : InfinitePlace F)
    (y : ((placeEquiv r w).Completion)ˣ) :
    pullIdele r (ideleSingleInfinite (placeEquiv r w) y) = ideleSingleInfinite w (archUnitsEquiv r w y) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w' => ?_) ?_
  · change phase_arch_local (r.symm : K →+* F) w'
        (((Pi.mulSingle (M := fun u : InfinitePlace K => (u.Completion)ˣ) (placeEquiv r w) y
          (placeEquiv r w')) : ((placeEquiv r w').Completion)ˣ) : (placeEquiv r w').Completion) =
      ((Pi.mulSingle (M := fun w : InfinitePlace F => (w.Completion)ˣ) w (archUnitsEquiv r w y) w' :
        (w'.Completion)ˣ) : w'.Completion)
    by_cases h : w' = w
    · subst h; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]; rfl
    · have h' : placeEquiv r w' ≠ placeEquiv r w := (placeEquiv r).injective.ne h
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, Units.val_one, Units.val_one]
      exact map_one (phase_arch_local (r.symm : K →+* F) w')
  · exact map_one (finitePull r)

theorem localComponentInfinite_transport (r : F ≃+* K) (χ : HeckeCharacter F) (w : InfinitePlace F)
    (y : ((placeEquiv r w).Completion)ˣ) :
    (transport r χ).localComponentInfinite (placeEquiv r w) y =
      χ.localComponentInfinite w (archUnitsEquiv r w y) := by
  unfold HeckeCharacter.localComponentInfinite
  rw [transport_apply, pullIdele_singleInfinite]

theorem isReal_placeEquiv (r : F ≃+* K) (w : InfinitePlace F) : (placeEquiv r w).IsReal ↔ w.IsReal :=
  isReal_comap_iff r.symm

theorem mult_placeEquiv (r : F ≃+* K) (w : InfinitePlace F) : (placeEquiv r w).mult = w.mult := by
  unfold InfinitePlace.mult
  by_cases h : w.IsReal
  · rw [if_pos h, if_pos ((isReal_placeEquiv r w).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((isReal_placeEquiv r w).1 h'))]

theorem norm_archUnitsEquiv (r : F ≃+* K) (w : InfinitePlace F) (y : ((placeEquiv r w).Completion)ˣ) :
    ‖((archUnitsEquiv r w y : (w.Completion)ˣ) : w.Completion)‖ = ‖(y : (placeEquiv r w).Completion)‖ := by
  rw [archUnitsEquiv_val]; exact arch_local_norm _ w _

/-- The two extension embeddings agree, or agree up to complex conjugation. -/
theorem emb_archUnitsEquiv (r : F ≃+* K) (w : InfinitePlace F) :
    (∀ y : ((placeEquiv r w).Completion)ˣ,
      Completion.extensionEmbedding w ((archUnitsEquiv r w y : (w.Completion)ˣ) : w.Completion) =
        Completion.extensionEmbedding (placeEquiv r w) (y : (placeEquiv r w).Completion)) ∨
    (∀ y : ((placeEquiv r w).Completion)ˣ,
      Completion.extensionEmbedding w ((archUnitsEquiv r w y : (w.Completion)ˣ) : w.Completion) =
        conj (Completion.extensionEmbedding (placeEquiv r w) (y : (placeEquiv r w).Completion))) := by
  rcases arch_local_emb (r.symm : K →+* F) w with h | h
  · exact Or.inl fun y => by rw [archUnitsEquiv_val]; exact h _
  · exact Or.inr fun y => by rw [archUnitsEquiv_val]; exact h _

theorem archExponent_transport (r : F ≃+* K) (χ : HeckeCharacter F) (w : InfinitePlace F) :
    (transport r χ).archExponent (placeEquiv r w) = χ.archExponent w := by
  set σw := placeEquiv r w
  set Φ := archUnitsEquiv r w
  have hrel : ∀ y : (σw.Completion)ˣ,
      ((Completion.extensionEmbedding w ((Φ y : (w.Completion)ˣ) : w.Completion)).im = 0 ↔
        (Completion.extensionEmbedding σw (y : σw.Completion)).im = 0) ∧
      (0 < (Completion.extensionEmbedding w ((Φ y : (w.Completion)ˣ) : w.Completion)).re ↔
        0 < (Completion.extensionEmbedding σw (y : σw.Completion)).re) := by
    intro y
    rcases emb_archUnitsEquiv r w with h | h
    · rw [h y]; exact ⟨Iff.rfl, Iff.rfl⟩
    · rw [h y, Complex.conj_im, Complex.conj_re, neg_eq_zero]; exact ⟨Iff.rfl, Iff.rfl⟩
  have hP : ∀ t : ℝ,
      (∀ y : (σw.Completion)ˣ, (Completion.extensionEmbedding σw (y : σw.Completion)).im = 0 →
        0 < (Completion.extensionEmbedding σw (y : σw.Completion)).re →
        (transport r χ).localComponentInfinite σw y =
          ((‖(y : σw.Completion)‖ ^ σw.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ↔
      (∀ x : (w.Completion)ˣ, (Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
        0 < (Completion.extensionEmbedding w (x : w.Completion)).re →
        χ.localComponentInfinite w x =
          ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) := by
    intro t
    constructor
    · intro h x h1 h2
      obtain ⟨y, rfl⟩ := Φ.surjective x
      rw [← localComponentInfinite_transport, norm_archUnitsEquiv, ← mult_placeEquiv r w]
      exact h y ((hrel y).1.1 h1) ((hrel y).2.1 h2)
    · intro h y h1 h2
      rw [localComponentInfinite_transport, ← norm_archUnitsEquiv, mult_placeEquiv]
      exact h (Φ y) ((hrel y).1.2 h1) ((hrel y).2.2 h2)
  unfold HeckeCharacter.archExponent
  by_cases hex : ∃ t : ℝ, ∀ x : (w.Completion)ˣ,
      (Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (Completion.extensionEmbedding w (x : w.Completion)).re →
      χ.localComponentInfinite w x =
        ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)
  · have hex' : ∃ t : ℝ, ∀ y : (σw.Completion)ˣ,
        (Completion.extensionEmbedding σw (y : σw.Completion)).im = 0 →
        0 < (Completion.extensionEmbedding σw (y : σw.Completion)).re →
        (transport r χ).localComponentInfinite σw y =
          ((‖(y : σw.Completion)‖ ^ σw.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) :=
      let ⟨t, ht⟩ := hex; ⟨t, (hP t).2 ht⟩
    rw [dif_pos hex', dif_pos hex]
    exact exponent_uniqueG w _ _ _ ((hP _).1 hex'.choose_spec) hex.choose_spec
  · have hex' : ¬ ∃ t : ℝ, ∀ y : (σw.Completion)ˣ,
        (Completion.extensionEmbedding σw (y : σw.Completion)).im = 0 →
        0 < (Completion.extensionEmbedding σw (y : σw.Completion)).re →
        (transport r χ).localComponentInfinite σw y =
          ((‖(y : σw.Completion)‖ ^ σw.mult : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) :=
      fun ⟨t, ht⟩ => hex ⟨t, (hP t).1 ht⟩
    rw [dif_neg hex', dif_neg hex]

theorem archParity_transport (r : F ≃+* K) (χ : HeckeCharacter F) (w : InfinitePlace F) :
    (transport r χ).archParity (placeEquiv r w) = χ.archParity w := by
  have hneg : archUnitsEquiv r w (-1) = -1 := Units.ext (by
    rw [archUnitsEquiv_val, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one]
    have h1 : phase_arch_local (r.symm : K →+* F) w 1 = 1 := map_one _
    exact (map_neg (phase_arch_local (r.symm : K →+* F) w) 1).trans (congrArg Neg.neg h1))
  unfold HeckeCharacter.archParity
  rw [localComponentInfinite_transport, hneg]

theorem archWeight_transport (r : F ≃+* K) (χ : HeckeCharacter F) (w : InfinitePlace F)
    (hw : w.IsComplex) :
    (transport r χ).archWeight (placeEquiv r w) = χ.archWeight w := by
  set σw := placeEquiv r w
  set Φ := archUnitsEquiv r w
  -- the sign relating the two weights
  obtain ⟨c, hc, hrel⟩ : ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ ∀ (y : (σw.Completion)ˣ) (n : ℤ),
      ‖(y : σw.Completion)‖ = 1 →
      (Completion.extensionEmbedding w ((Φ y : (w.Completion)ˣ) : w.Completion)) ^ (c * n) =
        (Completion.extensionEmbedding σw (y : σw.Completion)) ^ n := by
    rcases emb_archUnitsEquiv r w with h | h
    · exact ⟨1, Or.inl rfl, fun y n _ => by rw [h y, one_mul]⟩
    · refine ⟨-1, Or.inr rfl, fun y n hy => ?_⟩
      have hn : ‖Completion.extensionEmbedding σw (y : σw.Completion)‖ = 1 := by
        rw [norm_extensionEmbeddingG]; exact hy
      have hz : Completion.extensionEmbedding σw (y : σw.Completion) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
      rw [h y, ← Complex.inv_eq_conj hn, neg_one_mul, zpow_neg, inv_zpow', zpow_neg, inv_inv]
  have hQ : ∀ n : ℤ,
      (∀ y : (σw.Completion)ˣ, ‖(y : σw.Completion)‖ = 1 →
        (transport r χ).localComponentInfinite σw y =
          (Completion.extensionEmbedding σw (y : σw.Completion)) ^ n) ↔
      (∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
        χ.localComponentInfinite w x = (Completion.extensionEmbedding w (x : w.Completion)) ^ (c * n)) := by
    intro n
    constructor
    · intro h x hx
      obtain ⟨y, rfl⟩ := Φ.surjective x
      rw [norm_archUnitsEquiv] at hx
      rw [← localComponentInfinite_transport, hrel y n hx]
      exact h y hx
    · intro h y hy
      rw [localComponentInfinite_transport, ← hrel y n hy]
      exact h (Φ y) (by rw [norm_archUnitsEquiv]; exact hy)
  have hcc : ∀ n : ℤ, c * (c * n) = n := by
    intro n; rcases hc with rfl | rfl <;> ring
  unfold HeckeCharacter.archWeight
  by_cases hex : ∃ n : ℤ, ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x = (Completion.extensionEmbedding w (x : w.Completion)) ^ n
  · have hex' : ∃ n : ℤ, ∀ y : (σw.Completion)ˣ, ‖(y : σw.Completion)‖ = 1 →
        (transport r χ).localComponentInfinite σw y =
          (Completion.extensionEmbedding σw (y : σw.Completion)) ^ n := by
      obtain ⟨n, hn⟩ := hex
      refine ⟨c * n, (hQ (c * n)).2 ?_⟩
      rw [hcc]; exact hn
    rw [dif_pos hex', dif_pos hex]
    have h1 := (hQ _).1 hex'.choose_spec
    have h2 := weight_uniqueG w hw _ _ _ h1 hex.choose_spec
    rw [← h2]
    rcases hc with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, Int.natAbs_neg]
  · have hex' : ¬ ∃ n : ℤ, ∀ y : (σw.Completion)ˣ, ‖(y : σw.Completion)‖ = 1 →
        (transport r χ).localComponentInfinite σw y =
          (Completion.extensionEmbedding σw (y : σw.Completion)) ^ n :=
      fun ⟨n, hn⟩ => hex ⟨c * n, (hQ n).1 hn⟩
    rw [dif_neg hex', dif_neg hex]

theorem archLFactor_transport (r : F ≃+* K) (χ : HeckeCharacter F) (w : InfinitePlace F) (s : ℂ) :
    (transport r χ).archLFactor (placeEquiv r w) s = χ.archLFactor w s := by
  unfold HeckeCharacter.archLFactor
  rw [archExponent_transport]
  by_cases h : w.IsReal
  · rw [if_pos ((isReal_placeEquiv r w).2 h), if_pos h, archParity_transport]
  · rw [if_neg (fun h' => h ((isReal_placeEquiv r w).1 h')), if_neg h,
      archWeight_transport r χ w (InfinitePlace.not_isReal_iff_isComplex.1 h)]

theorem gammaFactor_transport (r : F ≃+* K) (χ : HeckeCharacter F) :
    (transport r χ).gammaFactor = χ.gammaFactor := by
  funext s
  unfold HeckeCharacter.gammaFactor
  rw [← (placeEquiv r).prod_comp]
  exact Finset.prod_congr rfl fun w _ => archLFactor_transport r χ w s

theorem completed_transport (r : F ≃+* K) (χ : HeckeCharacter F) :
    completedHeckeLFunction (transport r χ) = completedHeckeLFunction χ := by
  unfold completedHeckeLFunction
  rw [gammaFactor_transport, heckeLFunction_transport]

end ArchTransport

/-! ### Transport of the idele norm -/

section NormTransport

open NumberField NumberField.InfinitePlace IsDedekindDomain TatePrimeTransport MasulloGRH

variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

theorem toNNReal_congr {e₁ e₂ : NNReal} (h₁ : e₁ ≠ 0) (h₂ : e₂ ≠ 0) (he : e₁ = e₂) (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal h₁ x = WithZeroMulInt.toNNReal h₂ x := by
  subst he; rfl

theorem norm_localEquiv_symm (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F))
    (z : (primeEquiv r v).adicCompletion K) : ‖(localEquiv r v).symm z‖ = ‖z‖ := by
  rw [FinitePlace.norm_def, FinitePlace.norm_def]
  have hv : Valued.v ((localEquiv r v).symm z) = Valued.v z := by
    have := localEquiv_valuation r v ((localEquiv r v).symm z)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  rw [hv]
  congr 1
  exact toNNReal_congr _ _ (by rw [absNorm_primeEquiv]) _

theorem ideleNorm_pull (r : F ≃+* K) (g : IdeleGroup K) :
    MasulloGRH.ideleNorm (pullIdele r g) = MasulloGRH.ideleNorm g := by
  unfold MasulloGRH.ideleNorm
  congr 1
  · rw [← (placeEquiv r).prod_comp]
    refine Finset.prod_congr rfl fun w _ => ?_
    change ‖phase_arch_local (r.symm : K →+* F) w ((g : AdeleRing (𝓞 K) K).1 (placeEquiv r w))‖ ^ w.mult =
      ‖(g : AdeleRing (𝓞 K) K).1 (placeEquiv r w)‖ ^ (placeEquiv r w).mult
    rw [arch_local_norm, mult_placeEquiv]
    rfl
  · rw [← finprod_comp_equiv (primeEquiv r)]
    congr 1
    funext v
    change ‖(localEquiv r v).symm ((g : AdeleRing (𝓞 K) K).2 (primeEquiv r v))‖ = _
    rw [norm_localEquiv_symm]

theorem isNormPower_transport (r : F ≃+* K) (χ : HeckeCharacter F) (t₀ : ℝ)
    (h : χ.IsNormPower t₀) : (transport r χ).IsNormPower t₀ := by
  intro g
  rw [transport_apply, h (pullIdele r g), ideleNorm_pull]

theorem isTrivialOnNormOne_of_transport (r : F ≃+* K) (χ : HeckeCharacter F)
    (h : (transport r χ).IsTrivialOnNormOne) : χ.IsTrivialOnNormOne := by
  intro g hg
  obtain ⟨g', rfl⟩ := (pullIdele r).surjective g
  rw [ideleNorm_pull] at hg
  rw [← transport_apply]
  exact h g' hg

end NormTransport



open NumberField

theorem exists_small_copy (F : Type u) [Field F] [NumberField F] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (F ≃+* K) := by
  have : Countable F := @Finsupp.Countable.of_moduleFinite F ℚ _ _ _ _ _
  have : Small.{0} F := Countable.toSmall F
  let r : F ≃+* Shrink.{0} F := (Shrink.ringEquiv F).symm
  exact ⟨Shrink.{0} F, inferInstance, NumberField.of_ringEquiv F (Shrink.{0} F) r, ⟨r⟩⟩

theorem solution (F : Type*) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) :
    ∃ (ε : ℂ) (Nf : ℝ), ‖ε‖ = 1 ∧ 0 < Nf ∧ ∀ s : ℂ,
      MasulloGRH.completedHeckeLFunction χ⁻¹ (1 - s) =
        ε * (Nf : ℂ) ^ (s - 1 / 2) * MasulloGRH.completedHeckeLFunction χ s := by
  obtain ⟨K, hK, hNK, ⟨r⟩⟩ := exists_small_copy F
  obtain ⟨ε, Nf, hε, hNf, hfe⟩ := MasulloTateBridge.functional_equation (transport r χ)
  refine ⟨ε, Nf, hε, hNf, fun s => ?_⟩
  have h := hfe s
  rw [← transport_inv, completed_transport, completed_transport] at h
  exact h
