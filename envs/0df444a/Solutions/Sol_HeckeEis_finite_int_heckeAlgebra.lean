-- Prove2me | solution 1 for HeckeEis.finite_int_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d972ffb8-651f-5f99-b519-e9cd465f7dae

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra

import Theorems.Thm_HeckeEis_exists_coeffH1par_map_ringHom
import Theorems.Thm_HeckeEis_exists_basis_coeffH1par_int_complex
import Theorems.Thm_HeckeEis_existsEichlerShimuraMapLinear
import Theorems.Thm_HeckeEis_eichlerShimuraMap_injective
import Theorems.Thm_HeckeEis_eichlerShimuraMap_heckeTLin
import Theorems.Thm_HeckeEis_coeffH1par_map_heckeT_comm
import Theorems.Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_finite_int_heckeAlgebra

set_option autoImplicit false

open scoped Manifold MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binaryFormRepSL binaryFormAlphaAdj coeffParabolicCocycles coeffH1par coeffH1parMk coeffHeckeFun eichlerShimuraMap exists_coeffH1par_map_ringHom exists_basis_coeffH1par_int_complex existsEichlerShimuraMapLinear eichlerShimuraMap_injective eichlerShimuraMap_heckeTLin coeffH1par_map_heckeT_comm exists_coeffH1par_linearMap_coeffHeckeFun binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj"
namespace HeckeFiniteSol
p2m_open "HeckeEis"

open CongruenceSubgroup
open scoped MatrixGroups

section B

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

def Bsub (L : Submodule ℤ H) (W : Submodule ℂ H) : Subring (Module.End ℂ H) where
  carrier := {φ | (∀ x ∈ L, φ x ∈ L) ∧ (∀ w ∈ W, φ w ∈ W)}
  mul_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun x hx => by rw [Module.End.mul_apply]; exact h1 _ (h3 x hx),
      fun w hw => by rw [Module.End.mul_apply]; exact h2 _ (h4 w hw)⟩
  one_mem' := ⟨fun x hx => by simpa using hx, fun w hw => by simpa using hw⟩
  add_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun x hx => by rw [LinearMap.add_apply]; exact L.add_mem (h1 x hx) (h3 x hx),
      fun w hw => by rw [LinearMap.add_apply]; exact W.add_mem (h2 w hw) (h4 w hw)⟩
  zero_mem' := ⟨fun x _ => by simp, fun w _ => by simp⟩
  neg_mem' := by
    rintro φ ⟨h1, h2⟩
    exact ⟨fun x hx => by rw [LinearMap.neg_apply]; exact L.neg_mem (h1 x hx),
      fun w hw => by rw [LinearMap.neg_apply]; exact W.neg_mem (h2 w hw)⟩

theorem single_intCast_eq_zsmul {t : ℕ} (i j : Fin t) (z : ℤ) :
    (Matrix.single i j (z : ℂ) : Matrix (Fin t) (Fin t) ℂ) = z • Matrix.single i j (1 : ℂ) := by
  ext i' j'
  rw [Matrix.smul_apply, Matrix.single_apply, Matrix.single_apply, smul_ite, smul_zero, Int.smul_one_eq_cast]

theorem finite_Bsub {t : ℕ} (c : Module.Basis (Fin t) ℂ H) (W : Submodule ℂ H) :
    Module.Finite ℤ ↥(Bsub (Submodule.span ℤ (Set.range c)) W) := by
  classical
  let L : Submodule ℤ H := Submodule.span ℤ (Set.range c)
  let E : Fin t × Fin t → Matrix (Fin t) (Fin t) ℂ := fun ij => Matrix.single ij.1 ij.2 1
  let MZ : Submodule ℤ (Matrix (Fin t) (Fin t) ℂ) := Submodule.span ℤ (Set.range E)
  haveI : Module.Finite ℤ ↥MZ := Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range E))

  let ι : ↥(Bsub L W) →+ Matrix (Fin t) (Fin t) ℂ :=
    { toFun := fun φ => LinearMap.toMatrix c c φ.1
      map_zero' := by simp
      map_add' := fun φ ψ => by simp }
  have hι : ∀ φ, ι φ = LinearMap.toMatrix c c φ.1 := fun φ => rfl
  have hmem : ∀ φ : ↥(Bsub L W), ι φ ∈ MZ := by
    intro φ
    have hcol : ∀ j, ∃ k : Fin t → ℤ, ∑ i, k i • c i = φ.1 (c j) := fun j =>
      (Submodule.mem_span_range_iff_exists_fun ℤ).mp (φ.2.1 _ (Submodule.subset_span ⟨j, rfl⟩))
    choose k hk using hcol
    have hentry : ∀ i j, LinearMap.toMatrix c c φ.1 i j = ((k j i : ℤ) : ℂ) := by
      intro i j
      rw [LinearMap.toMatrix_apply, ← hk j]
      simp only [← Int.cast_smul_eq_zsmul ℂ, map_sum, map_smul, Module.Basis.repr_self, Finset.sum_apply',
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hM : ι φ = ∑ i, ∑ j, (k j i : ℤ) • E (i, j) := by
      rw [hι, Matrix.matrix_eq_sum_single (LinearMap.toMatrix c c φ.1)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hentry, single_intCast_eq_zsmul]
    rw [hM]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hinj : Function.Injective ι := by
    intro φ ψ h
    rw [hι, hι] at h
    exact Subtype.ext ((LinearMap.toMatrix c c).injective h)
  let ιZ : ↥(Bsub L W) →ₗ[ℤ] ↥MZ := LinearMap.codRestrict MZ ι.toIntLinearMap hmem
  have hinjZ : Function.Injective ιZ := by
    intro φ ψ h
    exact hinj (congrArg Subtype.val h)
  exact Module.Finite.of_injective ιZ hinjZ

end B

section R

variable {S H : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup H] [Module ℂ H]
variable (ES : S →ₗ[ℂ] H) (hinj : Function.Injective ES) (L : Submodule ℤ H)

def rfun (φ : ↥(Bsub L (LinearMap.range ES))) (f : S) : S :=
  Classical.choose (LinearMap.mem_range.mp (φ.2.2 (ES f) (LinearMap.mem_range_self ES f)))

theorem ES_rfun (φ : ↥(Bsub L (LinearMap.range ES))) (f : S) : ES (rfun ES L φ f) = φ.1 (ES f) :=
  Classical.choose_spec (LinearMap.mem_range.mp (φ.2.2 (ES f) (LinearMap.mem_range_self ES f)))

include hinj

def rLin (φ : ↥(Bsub L (LinearMap.range ES))) : Module.End ℂ S where
  toFun := rfun ES L φ
  map_add' f g := hinj (by rw [map_add, ES_rfun, ES_rfun, ES_rfun, map_add, map_add])
  map_smul' a f := hinj (by rw [map_smul, ES_rfun, ES_rfun, map_smul, map_smul]; rfl)

theorem ES_rLin (φ : ↥(Bsub L (LinearMap.range ES))) (f : S) : ES (rLin ES hinj L φ f) = φ.1 (ES f) :=
  ES_rfun ES L φ f

def rHom : ↥(Bsub L (LinearMap.range ES)) →+* Module.End ℂ S where
  toFun := rLin ES hinj L
  map_one' := LinearMap.ext fun f => hinj (by rw [ES_rLin]; rfl)
  map_mul' φ ψ := LinearMap.ext fun f => hinj (by
    rw [ES_rLin, Module.End.mul_apply, ES_rLin, ES_rLin]; rfl)
  map_zero' := LinearMap.ext fun f => hinj (by rw [ES_rLin, LinearMap.zero_apply, map_zero]; rfl)
  map_add' φ ψ := LinearMap.ext fun f => hinj (by
    rw [ES_rLin, LinearMap.add_apply, map_add, ES_rLin, ES_rLin]; rfl)

theorem ES_rHom (φ : ↥(Bsub L (LinearMap.range ES))) (f : S) : ES (rHom ES hinj L φ f) = φ.1 (ES f) :=
  ES_rfun ES L φ f

theorem finite_range_rHom [Module.Finite ℤ ↥(Bsub L (LinearMap.range ES))] :
    Module.Finite ℤ ↥(rHom ES hinj L).range :=
  Module.Finite.of_surjective (rHom ES hinj L).rangeRestrict.toAddMonoidHom.toIntLinearMap
    (rHom ES hinj L).rangeRestrict_surjective

end R

end HeckeEis.HeckeFiniteSol

end

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binaryFormRepSL binaryFormAlphaAdj coeffParabolicCocycles coeffH1par coeffH1parMk coeffHeckeFun eichlerShimuraMap exists_coeffH1par_map_ringHom exists_basis_coeffH1par_int_complex existsEichlerShimuraMapLinear eichlerShimuraMap_injective eichlerShimuraMap_heckeTLin coeffH1par_map_heckeT_comm exists_coeffH1par_linearMap_coeffHeckeFun binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj"
namespace HeckeFiniteSol
p2m_open "HeckeEis"

open CongruenceSubgroup
open scoped MatrixGroups

section Ops
variable (N n : ℕ)

def TZ (ℓ : ℕ) [NeZero ℓ] : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) →ₗ[ℤ] coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) :=
  Classical.choose (HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℤ n ℓ)
    (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℤ n N ℓ))

theorem TZ_spec (ℓ : ℕ) [NeZero ℓ] : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)),
      (w : Gamma0 N → ↥(BinaryForm ℤ n)) = coeffHeckeFun N ℓ ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℤ n ℓ) z ∧
        TZ N n ℓ (coeffH1parMk _ z) = coeffH1parMk _ w :=
  Classical.choose_spec (HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℤ n ℓ)
    (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℤ n N ℓ))

def TC (ℓ : ℕ) [NeZero ℓ] : coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) →ₗ[ℂ] coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) :=
  Classical.choose (HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℂ n ℓ)
    (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ))

theorem TC_spec (ℓ : ℕ) [NeZero ℓ] : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
      (w : Gamma0 N → ↥(BinaryForm ℂ n)) = coeffHeckeFun N ℓ ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℂ n ℓ) z ∧
        TC N n ℓ (coeffH1parMk _ z) = coeffH1parMk _ w :=
  Classical.choose_spec (HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℂ n ℓ)
    (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ))

end Ops

section Gen

variable (N : ℕ) [NeZero N] (n : ℕ)

theorem TC_basis {t : ℕ} (Φ : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) →+ coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
      (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
          = MvPolynomial.map (Int.castRingHom ℂ) (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
      Φ (coeffH1parMk _ z) = coeffH1parMk _ w)
    (b : Module.Basis (Fin t) ℤ (coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype))) (c : Module.Basis (Fin t) ℂ (coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)))
    (hbc : ∀ i, c i = Φ (b i)) (ℓ : ℕ) [NeZero ℓ] (j : Fin t) :
    TC N n ℓ (c j) = ∑ i, ((LinearMap.toMatrix b b (TZ N n ℓ) i j : ℤ) : ℂ) • c i := by
  have hcomm := HeckeEis.coeffH1par_map_heckeT_comm (Int.castRingHom ℂ) n N ℓ Φ hΦ (TZ N n ℓ) (TZ_spec N n ℓ)
    (TC N n ℓ) (TC_spec N n ℓ) (b j)
  have h1 : TC N n ℓ (c j) = Φ (TZ N n ℓ (b j)) := by rw [hbc j]; exact hcomm
  refine h1.trans ?_
  conv_lhs => rw [← b.sum_repr (TZ N n ℓ (b j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, LinearMap.toMatrix_apply, hbc i, Int.cast_smul_eq_zsmul]

theorem TC_mem_Bsub {t : ℕ} (Φ : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) →+ coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
      (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
          = MvPolynomial.map (Int.castRingHom ℂ) (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
      Φ (coeffH1parMk _ z) = coeffH1parMk _ w)
    (b : Module.Basis (Fin t) ℤ (coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype))) (c : Module.Basis (Fin t) ℂ (coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)))
    (hbc : ∀ i, c i = Φ (b i))
    (ES : CuspForm (Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ] coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
    (hES : ∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2), ES f = eichlerShimuraMap n N f)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    TC N n ℓ ∈ Bsub (Submodule.span ℤ (Set.range c)) (LinearMap.range ES) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨?_, ?_⟩
  ·
    have hgen : ∀ j, TC N n ℓ (c j) ∈ Submodule.span ℤ (Set.range c) := by
      intro j
      rw [TC_basis N n Φ hΦ b c hbc ℓ j]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hle : Submodule.span ℤ (Set.range c)
        ≤ (Submodule.span ℤ (Set.range c)).comap (TC N n ℓ).toAddMonoidHom.toIntLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgen j
    intro x hx
    exact hle hx
  ·
    rintro _ ⟨f, rfl⟩
    refine ⟨CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f, ?_⟩
    have h := HeckeEis.eichlerShimuraMap_heckeTLin N n hℓ hℓN (TC N n ℓ)
      (fun z => by obtain ⟨w, h1, h2⟩ := TC_spec N n ℓ z; exact ⟨w, h1, h2⟩) f
    rw [hES, hES]
    exact h.symm

theorem rHom_TC {t : ℕ} (Φ : coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) →+ coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
      (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ)
          = MvPolynomial.map (Int.castRingHom ℂ) (((z : Gamma0 N → ↥(BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
      Φ (coeffH1parMk _ z) = coeffH1parMk _ w)
    (b : Module.Basis (Fin t) ℤ (coeffH1par ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype))) (c : Module.Basis (Fin t) ℂ (coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)))
    (hbc : ∀ i, c i = Φ (b i))
    (ES : CuspForm (Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ] coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
    (hES : ∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2), ES f = eichlerShimuraMap n N f) (hinj : Function.Injective ES)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rHom ES hinj (Submodule.span ℤ (Set.range c)) ⟨TC N n ℓ, TC_mem_Bsub N n Φ hΦ b c hbc ES hES hℓ hℓN⟩
      = (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN : Module.End ℂ (CuspForm (Gamma0 N) ((n : ℤ) + 2))) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine LinearMap.ext fun f => hinj ?_
  rw [ES_rHom]
  have h := HeckeEis.eichlerShimuraMap_heckeTLin N n hℓ hℓN (TC N n ℓ)
    (fun z => by obtain ⟨w, h1, h2⟩ := TC_spec N n ℓ z; exact ⟨w, h1, h2⟩) f
  show TC N n ℓ (ES f) = ES (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f)
  rw [hES, hES]
  exact h

end Gen

end HeckeEis.HeckeFiniteSol

end

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_finite_int_heckeAlgebra.HeckeEis HeckeEis.HeckeFiniteSol CongruenceSubgroup in
theorem solution (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) :
    Module.Finite ℤ ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) := by
  classical
  obtain ⟨Φ, hΦ⟩ := HeckeEis.exists_coeffH1par_map_ringHom (Int.castRingHom ℂ) n (CongruenceSubgroup.Gamma0 N)
  obtain ⟨t, b, c, hbc⟩ := HeckeEis.exists_basis_coeffH1par_int_complex n N Φ hΦ
  obtain ⟨ES, hES⟩ := HeckeEis.existsEichlerShimuraMapLinear n N
  have hinj : Function.Injective ES := by
    intro f g h
    apply HeckeEis.eichlerShimuraMap_injective N n
    show HeckeEis.eichlerShimuraMap n N f = HeckeEis.eichlerShimuraMap n N g
    rw [← hES, ← hES, h]
  let L : Submodule ℤ (coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)) := Submodule.span ℤ (Set.range c)
  haveI : Module.Finite ℤ ↥(Bsub L (LinearMap.range ES)) := finite_Bsub c (LinearMap.range ES)
  haveI hfin : Module.Finite ℤ ↥(rHom ES hinj L).range := finite_range_rHom ES hinj L

  have hle : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S ≤ subalgebraOfSubring (rHom ES hinj L).range := by
    refine Algebra.adjoin_le ?_
    rintro T (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
    · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      show _ ∈ (rHom ES hinj L).range
      exact ⟨⟨TC N n ℓ, TC_mem_Bsub N n Φ hΦ b c hbc ES hES hℓ hℓN⟩, rHom_TC N n Φ hΦ b c hbc ES hES hinj hℓ hℓN⟩
    · exact absurd (hS q hq hqN) hqS

  let incl : ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) →+ ↥(rHom ES hinj L).range :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hincl : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun z : ↥(rHom ES hinj L).range => (z : Module.End ℂ (CuspForm (Gamma0 N) ((n : ℤ) + 2)))) h)
  exact Module.Finite.of_injective incl.toIntLinearMap hincl

end S_HeckeEis_finite_int_heckeAlgebra
end P2MW
export P2MW.S_HeckeEis_finite_int_heckeAlgebra (solution)
