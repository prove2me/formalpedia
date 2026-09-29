-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3aaada05-a0b9-5a9d-8e2e-ad513ec9646e

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

import Theorems.Thm_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace SSJ2

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

theorem law_of_mem_span (f : G → ℂ) (a : G) (χ : ℂ) (hf : ∀ g : G, f (a * g) = χ * f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∀ g : G, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace G] [ContinuousMul G]

theorem exists_open_stabilizer_of_mem_span (f : G → ℂ) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ k ∈ K, ∀ g : G, f (g * k) = f g) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk
        show f (g * k * h) = f (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by simp only [mul_assoc, mul_inv_cancel_left]]
        exact hf _ hk (g * h)
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · intro k hk g
        rw [Subgroup.mem_inf] at hk
        simp only [Pi.add_apply, hW₁ k hk.1 g, hW₂ k hk.2 g]
  | smul c W _ h₁ =>
      obtain ⟨U, hU, hWU⟩ := h₁
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hWU k hk g]⟩

end Generic

end SSJ2

namespace WBJ2

open FLT.SmoothAdmissibleSchurCommutant

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

def rT (h : G2) : (G2 → ℂ) →ₗ[ℂ] (G2 → ℂ) where
  toFun f := fun g => f (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rT_apply (h : G2) (f : G2 → ℂ) (g : G2) : rT p h f g = f (g * h) := rfl

def piV (V : Submodule ℂ (G2 → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G2, (fun g => W (g * h)) ∈ V) :
    G2 →* Module.End ℂ V where
  toFun h := (rT p h).restrict (fun W hW => hstab W hW h)
  map_one' := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    funext g; simp
  map_mul' h₁ h₂ := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    rw [Module.End.mul_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
    funext g; simp [mul_assoc]

theorem piV_apply_coe (V : Submodule ℂ (G2 → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G2, (fun g => W (g * h)) ∈ V)
    (h : G2) (v : V) : ((piV p V hstab h v : V) : G2 → ℂ) = fun g => (v : G2 → ℂ) (g * h) := by
  show (((rT p h).restrict (fun W hW => hstab W hW h)) v : G2 → ℂ) = _
  rw [LinearMap.coe_restrict_apply]
  rfl

theorem unipotentGL2_eq (x : F) : (AutomorphicForm.unipotentGL2 x : G2) = unipotent x := Units.ext rfl

theorem diagOne_mul_unipotent (y : (F)ˣ) (t : F) :
    (diagOne y : G2) * unipotent t = unipotent ((y : F) * t) * diagOne y := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (diagOne y : G2).1 * !![(1 : F), t; 0, 1] = !![(1 : F), (y : F) * t; 0, 1] * (diagOne y : G2).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, NumberField.AdelicLevel.diagOne_coe_apply, Matrix.diagonal]

theorem main
    (θ₀ : (F)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : G2 → ℂ)
    (hw₂law : ∀ (x : F) (g : G2), w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G2, w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w (g * h)))
    (hw₂adm : ∀ U : Subgroup G2, IsOpen (U : Set G2) →
      ∃ B : Finset (G2 → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : G2, w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (G2 → ℂ)))
    (hcentral : ∀ (z : (F)ˣ) (g : G2), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    (∀ v ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)),
        ∃ N₀ : ℤ, ∀ y : (F)ˣ, Valued.v (y : F) ≤ WithZero.exp N₀ → v (diagOne y) = 0) ∨
      (∃ (χ₁ ω₁ : (F)ˣ →* ℂˣ) (ℓB : (G2 → ℂ) →ₗ[ℂ] ℂ),
        (∃ v ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)), ℓB v ≠ 0) ∧
        (∀ (x : F), ∀ v ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)),
          ℓB (fun g : G2 => v (g * unipotent x)) = ℓB v) ∧
        (∀ (a : (F)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)),
          ℓB (fun g : G2 => v (g * diagOne a)) = ((χ₁ a : ℂˣ) : ℂ) * ℓB v) ∧
        (∀ (a : (F)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)),
          ℓB (fun g : G2 => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ((ω₁ a : ℂˣ) : ℂ) * ℓB v)) := by
  classical
  set V : Submodule ℂ (G2 → ℂ) := Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)) with hV
  have hNopen : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set G2) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have Vstab : ∀ W ∈ V, ∀ h : G2, (fun g => W (g * h)) ∈ V := fun W hW h => SSJ2.translate_mem_span w₂base h hW
  have Vlaw : ∀ W ∈ V, ∀ (x : F) (g : G2), W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    fun W hW x => SSJ2.law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hW
  have Vsm : ∀ W ∈ V, ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g :=
    fun W hW => SSJ2.exists_open_stabilizer_of_mem_span w₂base _ hNopen hw₂K hW
  have hw₂V : w₂base ∈ V := Submodule.subset_span ⟨1, funext fun g => by show w₂base (g * 1) = w₂base g; rw [mul_one]⟩

  set S : Set (G2 → ℂ) := {D : G2 → ℂ | ∃ W' ∈ V, ∃ t : F, D = fun g : G2 => W' (g * unipotent t) - W' g} with hS
  by_cases hcusp : ∀ W ∈ V, W ∈ Submodule.span ℂ S
  ·
    left
    intro v hv
    have hmem := hcusp v hv
    clear hv
    induction hmem using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨W', hW', t, rfl⟩ := hD
        by_cases ht : t = 0
        · refine ⟨0, fun y _ => ?_⟩
          show W' (diagOne y * unipotent t) - W' (diagOne y) = 0
          have : (unipotent t : G2) = 1 := by
            apply Units.ext; rw [ht]; show !![(1 : F), 0; 0, 1] = 1
            ext i j; fin_cases i <;> fin_cases j <;> simp
          rw [this, mul_one, sub_self]
        · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
          set k : ℤ := WithZero.log (Valued.v t) with hk
          have hvt' : Valued.v t = WithZero.exp k := by rw [hk, WithZero.exp_log hvt]
          refine ⟨-k, fun y hy => ?_⟩
          show W' (diagOne y * unipotent t) - W' (diagOne y) = 0
          rw [diagOne_mul_unipotent, Vlaw W' hW', LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p _ ?_,
            one_mul, sub_self]
          rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hvt']
          calc Valued.v (y : F) * WithZero.exp k ≤ WithZero.exp (-k) * WithZero.exp k := mul_le_mul_left hy _
            _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    | zero => exact ⟨0, fun y _ => rfl⟩
    | add D₁ D₂ _ _ h₁ h₂ =>
        obtain ⟨N₁, hN₁⟩ := h₁
        obtain ⟨N₂, hN₂⟩ := h₂
        refine ⟨min N₁ N₂, fun y hy => ?_⟩
        show D₁ (diagOne y) + D₂ (diagOne y) = 0
        rw [hN₁ y (hy.trans (WithZero.exp_le_exp.2 (min_le_left _ _))),
          hN₂ y (hy.trans (WithZero.exp_le_exp.2 (min_le_right _ _))), add_zero]
    | smul c D _ h₁ =>
        obtain ⟨N₁, hN₁⟩ := h₁
        exact ⟨N₁, fun y hy => by show c • D (diagOne y) = 0; rw [hN₁ y hy, smul_zero]⟩
  ·
    right
    push Not at hcusp
    obtain ⟨W₀, hW₀V, hW₀⟩ := hcusp
    set π : G2 →* Module.End ℂ V := piV p V Vstab with hπdef
    have hπcoe : ∀ (h : G2) (v : V), ((π h v : V) : G2 → ℂ) = fun g => (v : G2 → ℂ) (g * h) :=
      fun h v => piV_apply_coe p V Vstab h v

    have hsmooth : IsSmoothRep π := by
      intro v
      obtain ⟨U, hU, hUv⟩ := Vsm (v : G2 → ℂ) v.2
      refine Subgroup.isOpen_mono (H₁ := U) (fun k hk => ?_) hU
      show π k v = v
      apply Subtype.ext
      rw [hπcoe]
      funext g; exact hUv k hk g

    have hadm : IsAdmissibleRep π := by
      intro K _ hKo
      obtain ⟨B, hB⟩ := hw₂adm K hKo
      haveI := FiniteDimensional.span_finset ℂ B
      have hrange : ∀ v : fixedVectors π K, (((v : V) : G2 → ℂ)) ∈ Submodule.span ℂ (B : Set (G2 → ℂ)) := by
        intro v
        refine hB _ (v : V).2 (fun k hk g => ?_)
        have := congrArg (fun z : V => (z : G2 → ℂ) g) (v.2 k hk)
        simpa [hπcoe] using this
      let f : fixedVectors π K →ₗ[ℂ] Submodule.span ℂ (B : Set (G2 → ℂ)) :=
        LinearMap.codRestrict _ (V.subtype.comp (fixedVectors π K).subtype) hrange
      have hf : Function.Injective f := by
        intro a b hab
        have h := congrArg Subtype.val hab
        simp only [f, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h
        exact Subtype.ext (Subtype.ext h)
      exact Module.Finite.of_injective f hf

    have hirr : IsIrreducibleRep π := by
      refine ⟨⟨⟨w₂base, hw₂V⟩, fun h => hw₂ne (congrArg Subtype.val h)⟩, fun W' hW' => ?_⟩
      by_cases hbot : W' = ⊥
      · exact Or.inl hbot
      right
      obtain ⟨v, hvW', hv0⟩ := (Submodule.ne_bot_iff W').1 hbot
      have hv0' : (v : G2 → ℂ) ≠ 0 := fun h => hv0 (Subtype.ext h)
      have h1 := hw₂irr (v : G2 → ℂ) v.2 hv0'
      have hTV : Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => (v : G2 → ℂ) (g * h)) ≤ V :=
        SSJ2.span_le_span_of_mem _ _ v.2
      have key : ∀ W : G2 → ℂ, W ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => (v : G2 → ℂ) (g * h)) →
          ∀ (hWV : W ∈ V), (⟨W, hWV⟩ : V) ∈ W' := by
        intro W hW
        induction hW using Submodule.span_induction with
        | mem W hWm =>
            obtain ⟨h, rfl⟩ := hWm
            intro hWV
            have e : (⟨fun g : G2 => (v : G2 → ℂ) (g * h), hWV⟩ : V) = π h v := Subtype.ext (by rw [hπcoe])
            rw [e]; exact hW' h v hvW'
        | zero => intro h0; exact W'.zero_mem
        | add W₁ W₂ hW₁ hW₂ h₁ h₂ =>
            intro h12
            have e : (⟨W₁ + W₂, h12⟩ : V) = ⟨W₁, hTV hW₁⟩ + ⟨W₂, hTV hW₂⟩ := rfl
            rw [e]; exact W'.add_mem (h₁ _) (h₂ _)
        | smul c W hW h₁ =>
            intro hcW
            have e : (⟨c • W, hcW⟩ : V) = c • ⟨W, hTV hW⟩ := rfl
            rw [e]; exact W'.smul_mem c (h₁ _)
      have hVT : V ≤ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => (v : G2 → ℂ) (g * h)) :=
        SSJ2.span_le_span_of_mem _ _ h1
      rw [eq_top_iff]
      intro u _
      have := key (u : G2 → ℂ) (hVT u.2) u.2
      exact this

    have hNtop : Submodule.span ℂ {y : V | ∃ (t : F) (z : V), y = π (AutomorphicForm.unipotentGL2 t) z - z} ≠ ⊤ := by
      intro htop
      apply hW₀
      have hmem : (⟨W₀, hW₀V⟩ : V) ∈
          Submodule.span ℂ {y : V | ∃ (t : F) (z : V), y = π (AutomorphicForm.unipotentGL2 t) z - z} := by
        rw [htop]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := V.subtype) hmem
      rw [Submodule.map_span] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨y, ⟨t, z, rfl⟩, rfl⟩
      refine ⟨(z : G2 → ℂ), z.2, t, ?_⟩
      show ((π (AutomorphicForm.unipotentGL2 t) z : V) : G2 → ℂ) - (z : G2 → ℂ) = _
      rw [hπcoe, unipotentGL2_eq]
      rfl
    obtain ⟨χ₁, ω₁, ℓ, hℓ0, hℓN, hℓD, hℓZ⟩ :=
      LocalGL2.exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top ℚ p π hsmooth hadm hirr hNtop
    obtain ⟨ℓB, hℓB⟩ := LinearMap.exists_extend ℓ
    have hℓBv : ∀ (v : G2 → ℂ) (hv : v ∈ V), ℓB v = ℓ ⟨v, hv⟩ := fun v hv => by rw [← hℓB]; rfl
    refine ⟨χ₁, ω₁, ℓB, ?_, ?_, ?_, ?_⟩
    · by_contra h
      push Not at h
      apply hℓ0
      ext v
      rw [← hℓB]
      show ℓB v = 0
      exact h v v.2
    · intro x v hv
      have e : (⟨fun g : G2 => v (g * unipotent x), Vstab v hv (unipotent x)⟩ : V) =
          π (AutomorphicForm.unipotentGL2 x) ⟨v, hv⟩ := Subtype.ext (by rw [hπcoe, unipotentGL2_eq])
      rw [hℓBv v hv, ← hℓN x ⟨v, hv⟩, hℓBv _ (Vstab v hv (unipotent x)), e]
    · intro a v hv
      have e : (⟨fun g : G2 => v (g * diagOne a), Vstab v hv (diagOne a)⟩ : V) = π (diagOne a) ⟨v, hv⟩ :=
        Subtype.ext (by rw [hπcoe])
      rw [hℓBv v hv, ← hℓD a ⟨v, hv⟩, hℓBv _ (Vstab v hv (diagOne a)), e]
    · intro a v hv
      have e : (⟨fun g : G2 => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a),
          Vstab v hv (Matrix.GeneralLinearGroup.scalar (Fin 2) a)⟩ : V) =
          π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) ⟨v, hv⟩ := Subtype.ext (by rw [hπcoe])
      rw [hℓBv v hv, ← hℓZ a ⟨v, hv⟩, hℓBv _ (Vstab v hv (Matrix.GeneralLinearGroup.scalar (Fin 2) a)), e]

end WBJ2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible.WBJ2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible.WBJ2"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    :
    (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) ∨
      (∃ (χ₁ ω₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (ℓB : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
        (∃ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB v ≠ 0) ∧
        (∀ (x : (p.adicCompletion ℚ)), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * unipotent x)) = ℓB v) ∧
        (∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * diagOne a)) = ((χ₁ a : ℂˣ) : ℂ) * ℓB v) ∧
        (∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ((ω₁ a : ℂˣ) : ℂ) * ℓB v)) :=
  WBJ2.main p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral

end S_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible (solution)
