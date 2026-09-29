-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isEnd_blowupChart_map_of_isLevelAutAt_of_mem_valuationSubring_iff_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/44b7f8b1-e511-54b1-9dd2-372f8082dc8e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isEnd_blowupChart_map_of_isLevelAutAt_of_mem_valuationSubring_iff_of_drinfeldChartWitness_linked
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace EndsPerm

def subringEquiv {K : Type} [Field K] (e : K ≃+* K) (S T : Subring K)
    (h₁ : ∀ x : K, x ∈ S → e x ∈ T) (h₂ : ∀ x : K, x ∈ T → e.symm x ∈ S) : ↥S ≃+* ↥T where
  toFun x := ⟨e (x : K), h₁ _ x.2⟩
  invFun y := ⟨e.symm (y : K), h₂ _ y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : K))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K))
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))

def subalgEquiv {A K : Type} [CommRing A] [Field K] [Algebra A K] (e : K ≃+* K) (S T : Subalgebra A K)
    (h₁ : ∀ x : K, x ∈ S → e x ∈ T) (h₂ : ∀ x : K, x ∈ T → e.symm x ∈ S) : ↥S ≃+* ↥T where
  toFun x := ⟨e (x : K), h₁ _ x.2⟩
  invFun y := ⟨e.symm (y : K), h₂ _ y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : K))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K))
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))

def valSubringEquiv {K : Type} [Field K] (e : K ≃+* K) (S T : ValuationSubring K)
    (h₁ : ∀ x : K, x ∈ S → e x ∈ T) (h₂ : ∀ x : K, x ∈ T → e.symm x ∈ S) : ↥S ≃+* ↥T where
  toFun x := ⟨e (x : K), h₁ _ x.2⟩
  invFun y := ⟨e.symm (y : K), h₂ _ y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : K))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K))
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))

theorem map_mem_adjoinDiv {A K F : Type} [CommRing A] [Field K] [Algebra A K] [FunLike F K K] [RingHomClass F K K]
    (C : Subalgebra A K) (J : Ideal ↥C) (σ : F) (a b : K) (hab : σ a = b)
    (hσC : ∀ x : K, x ∈ C → σ x ∈ C)
    (hσJ : ∀ (i : ↥C) (hi : σ (i : K) ∈ C), i ∈ J → (⟨σ (i : K), hi⟩ : ↥C) ∈ J) :
    ∀ f : K, f ∈ (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * a = ((i : ↥C) : K)}).restrictScalars A →
      σ f ∈ (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * b = ((i : ↥C) : K)}).restrictScalars A := by
  intro f hf
  rw [Subalgebra.mem_restrictScalars] at hf ⊢
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hiJ, hx⟩ := hx
      refine Algebra.subset_adjoin ?_
      refine ⟨⟨σ (i : K), hσC _ i.2⟩, hσJ i _ hiJ, ?_⟩
      simp only
      rw [← hab, ← map_mul, hx]
  | algebraMap c =>
      have hc : σ ((c : ↥C) : K) ∈ C := hσC _ c.2
      have : σ (algebraMap (↥C) K c) = algebraMap (↥C) K ⟨σ (c : K), hc⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem transport {A K : Type} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (J y : Ideal ↥C) (B : Subalgebra A K) (ϖ : A)
    (W : ValuationSubring K)
    (e : K ≃+* K) (τ : K → K) (hτe : ∀ x : K, τ x = e x)
    (hC : ∀ x : K, x ∈ C ↔ τ x ∈ C)
    (hJ : ∀ (a : ↥C) (ha : τ (a : K) ∈ C), a ∈ J ↔ (⟨τ (a : K), ha⟩ : ↥C) ∈ J)
    (hBτ : ∀ f : K, f ∈ B → τ f ∈ B)
    (hWτ : ∀ f : K, f ∈ W ↔ τ f ∈ W)
    (hyW : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hϖ : τ (algebraMap A K ϖ) = algebraMap A K ϖ)
    (O : Subring K)
    (hO : ∃ (a : ↥C) (_ : a ∈ J) (_ : ((a : ↥C) : K) ≠ 0),
          let Ba : Subalgebra A K := (Algebra.adjoin ↥C
            {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)) ∧
            (∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O, ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : K, f ∈ B → f ∈ O)) :
    ∃ O' : Subring K,
        (∃ (a : ↥C) (_ : a ∈ J) (_ : ((a : ↥C) : K) ≠ 0),
          let Ba : Subalgebra A K := (Algebra.adjoin ↥C
            {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : K, f ∈ O' ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)) ∧
            (∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O', ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O')) ∧
            ¬ (∀ f : K, f ∈ B → f ∈ O')) ∧
        (∀ f : K, f ∈ O ↔ τ f ∈ O') ∧
        (∀ 𝔭 𝔭' : Ideal ↥C, (𝔭.IsPrime ∧ algebraMap A ↥C ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) →
          (𝔭'.IsPrime ∧ algebraMap A ↥C ϖ ∈ 𝔭' ∧ 𝔭' ≤ y ∧ 𝔭' ≠ y) →
          (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A K ϖ ∈ O, (⟨algebraMap A K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥C, b ∈ y ∧ ∀ hb : ((b : ↥C) : K) ∈ O, (⟨((b : ↥C) : K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥C) : K), hc⟩ : ↥O) ∈ 𝔮)) →
          (∀ (c : ↥C) (hc : τ (c : K) ∈ C), c ∈ 𝔭 ↔ (⟨τ (c : K), hc⟩ : ↥C) ∈ 𝔭') →
          (∃ 𝔮 : Ideal ↥O', 𝔮.IsPrime ∧
            (∀ h : algebraMap A K ϖ ∈ O', (⟨algebraMap A K ϖ, h⟩ : ↥O') ∈ 𝔮) ∧
            (∃ b : ↥C, b ∈ y ∧ ∀ hb : ((b : ↥C) : K) ∈ O', (⟨((b : ↥C) : K), hb⟩ : ↥O') ∉ 𝔮) ∧
            (∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ O'),
              c ∈ 𝔭' ↔ (⟨((c : ↥C) : K), hc⟩ : ↥O') ∈ 𝔮))) := by
  classical
  have hτe' : τ = ⇑e := funext hτe
  subst hτe'
  obtain ⟨a, haJ, ha0, P, hPmax, hOloc, hOy, hOB⟩ := hO

  have hC' : ∀ x : K, e.symm x ∈ C ↔ x ∈ C := by
    intro x
    have h := hC (e.symm x)
    rw [e.apply_symm_apply] at h
    exact h
  have hCfwd : ∀ x : K, x ∈ C → e x ∈ C := fun x hx => (hC x).mp hx
  have hCbwd : ∀ x : K, x ∈ C → e.symm x ∈ C := fun x hx => (hC' x).mpr hx
  have hJfwd : ∀ (i : ↥C) (hi : e (i : K) ∈ C), i ∈ J → (⟨e (i : K), hi⟩ : ↥C) ∈ J :=
    fun i hi h => (hJ i hi).mp h
  have hJbwd : ∀ (i : ↥C) (hi : e.symm (i : K) ∈ C), i ∈ J → (⟨e.symm (i : K), hi⟩ : ↥C) ∈ J := by
    intro i hi hiJ
    have h2 : e ((⟨e.symm (i : K), hi⟩ : ↥C) : K) ∈ C := by
      show e (e.symm (i : K)) ∈ C
      rw [e.apply_symm_apply]; exact i.2
    apply (hJ ⟨e.symm (i : K), hi⟩ h2).mpr
    have h3 : (⟨e ((⟨e.symm (i : K), hi⟩ : ↥C) : K), h2⟩ : ↥C) = i := Subtype.ext (e.apply_symm_apply _)
    rw [h3]; exact hiJ
  have hϖ' : e.symm (algebraMap A K ϖ) = algebraMap A K ϖ := by
    conv_lhs => rw [← hϖ]
    exact e.symm_apply_apply _

  let ω : ↥W ≃+* ↥W := valSubringEquiv e W W (fun x hx => (hWτ x).mp hx)
    (fun x hx => by rw [hWτ, e.apply_symm_apply]; exact hx)
  have hωmax : ∀ x : ↥W, x ∈ maximalIdeal ↥W ↔ ω x ∈ maximalIdeal ↥W := by
    intro x
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx hu
      apply hx
      have h := hu.map ω.symm
      rwa [ω.symm_apply_apply] at h
    · intro hx hu
      exact hx (hu.map ω)
  have hy : ∀ (b : ↥C) (hb : e (b : K) ∈ C), b ∈ y ↔ (⟨e (b : K), hb⟩ : ↥C) ∈ y := by
    intro b hb
    rw [hyW, hyW]
    constructor
    · rintro ⟨hbW, hbm⟩
      refine ⟨(hWτ (b : K)).mp hbW, ?_⟩
      have key : (⟨((⟨e (b : K), hb⟩ : ↥C) : K), (hWτ (b : K)).mp hbW⟩ : ↥W) = ω ⟨(b : K), hbW⟩ :=
        Subtype.ext rfl
      rw [key]
      exact (hωmax _).mp hbm
    · rintro ⟨hbW', hbm'⟩
      have hbW : (b : K) ∈ W := (hWτ (b : K)).mpr hbW'
      refine ⟨hbW, ?_⟩
      apply (hωmax _).mpr
      have key : ω ⟨(b : K), hbW⟩ = (⟨((⟨e (b : K), hb⟩ : ↥C) : K), hbW'⟩ : ↥W) := Subtype.ext rfl
      rw [key]
      exact hbm'
  have hy' : ∀ (b : ↥C) (hb : e.symm (b : K) ∈ C), b ∈ y → (⟨e.symm (b : K), hb⟩ : ↥C) ∈ y := by
    intro b hb hby
    have h2 : e ((⟨e.symm (b : K), hb⟩ : ↥C) : K) ∈ C := by
      show e (e.symm (b : K)) ∈ C
      rw [e.apply_symm_apply]; exact b.2
    apply (hy ⟨e.symm (b : K), hb⟩ h2).mpr
    have h3 : (⟨e ((⟨e.symm (b : K), hb⟩ : ↥C) : K), h2⟩ : ↥C) = b := Subtype.ext (e.apply_symm_apply _)
    rw [h3]; exact hby

  let O' : Subring K := O.map e.toRingHom
  have memO' : ∀ f : K, f ∈ O' ↔ e.symm f ∈ O := by
    intro f
    constructor
    · rintro ⟨x, hx, hfx⟩
      rw [← hfx]
      show e.symm (e x) ∈ O
      rw [e.symm_apply_apply]; exact hx
    · intro h
      exact ⟨e.symm f, h, e.apply_symm_apply f⟩
  have memO'e : ∀ f : K, f ∈ O ↔ e f ∈ O' := by
    intro f; rw [memO', e.symm_apply_apply]
  let ψ : ↥O ≃+* ↥O' := subringEquiv e O O' (fun x hx => (memO'e x).mp hx) (fun x hx => (memO' x).mp hx)
  refine ⟨O', ?_, memO'e, ?_⟩
  ·
    have haC : e (a : K) ∈ C := hCfwd _ a.2
    refine ⟨⟨e (a : K), haC⟩, hJfwd a haC haJ, ?_, ?_⟩
    · show e (a : K) ≠ 0
      exact (map_ne_zero_iff e e.injective).mpr ha0
    intro Ba'

    have fwd : ∀ x : K, x ∈ (Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A → e x ∈ Ba' :=
      map_mem_adjoinDiv C J e ((a : ↥C) : K) ((⟨e (a : K), haC⟩ : ↥C) : K) rfl hCfwd hJfwd
    have bwd : ∀ x : K, x ∈ Ba' → e.symm x ∈ (Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A :=
      map_mem_adjoinDiv C J e.symm ((⟨e (a : K), haC⟩ : ↥C) : K) ((a : ↥C) : K) (e.symm_apply_apply _) hCbwd hJbwd
    let φ : ↥((Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A) ≃+* ↥Ba' :=
      subalgEquiv e _ Ba' fwd bwd
    haveI : P.IsMaximal := hPmax
    refine ⟨Ideal.comap φ.symm P, Ideal.comap_isMaximal_of_equiv φ.symm, ?_, ?_, ?_⟩
    ·
      intro f
      rw [memO', hOloc]
      constructor
      · rintro ⟨g, h, hhP, hfe⟩
        refine ⟨φ g, φ h, ?_, ?_⟩
        · rwa [Ideal.mem_comap, φ.symm_apply_apply]
        · show f * e (h : K) = e (g : K)
          have h1 := congrArg e hfe
          rw [map_mul, e.apply_symm_apply] at h1
          exact h1
      · rintro ⟨g, h, hhP, hfe⟩
        refine ⟨φ.symm g, φ.symm h, ?_, ?_⟩
        · rwa [Ideal.mem_comap] at hhP
        · show e.symm f * e.symm (h : K) = e.symm (g : K)
          rw [← map_mul, hfe]
    ·
      intro b hby hb hunit
      have hb' : e.symm (b : K) ∈ O := (memO' _).mp hb
      have hbC : e.symm (b : K) ∈ C := hCbwd _ b.2
      apply hOy ⟨e.symm (b : K), hbC⟩ (hy' b hbC hby) hb'
      have key : ψ.symm ⟨(b : K), hb⟩ = ⟨((⟨e.symm (b : K), hbC⟩ : ↥C) : K), hb'⟩ := Subtype.ext rfl
      rw [← key]
      exact hunit.map ψ.symm
    ·
      intro hall
      apply hOB
      intro f hfB
      have h1 : e f ∈ O' := hall (e f) (hBτ f hfB)
      exact (memO'e f).mpr h1
  ·
    rintro 𝔭 𝔭' - - ⟨𝔮, h𝔮p, hϖ𝔮, ⟨b, hby, hb𝔮⟩, hc𝔮⟩ hpp'
    haveI : 𝔮.IsPrime := h𝔮p
    refine ⟨Ideal.comap ψ.symm 𝔮, Ideal.comap_isPrime ψ.symm 𝔮, ?_, ?_, ?_⟩
    · intro h
      have h0 : algebraMap A K ϖ ∈ O := by
        have h1 := (memO' _).mp h
        rwa [hϖ'] at h1
      rw [Ideal.mem_comap]
      have key : ψ.symm ⟨algebraMap A K ϖ, h⟩ = ⟨algebraMap A K ϖ, h0⟩ := Subtype.ext hϖ'
      rw [key]
      exact hϖ𝔮 h0
    · refine ⟨⟨e (b : K), hCfwd _ b.2⟩, (hy b (hCfwd _ b.2)).mp hby, ?_⟩
      intro hb'
      have hbO : (b : K) ∈ O := by
        have h1 : e.symm (e (b : K)) ∈ O := (memO' _).mp hb'
        rwa [e.symm_apply_apply] at h1
      rw [Ideal.mem_comap]
      have key : ψ.symm ⟨((⟨e (b : K), hCfwd _ b.2⟩ : ↥C) : K), hb'⟩ = ⟨(b : K), hbO⟩ :=
        Subtype.ext (e.symm_apply_apply _)
      rw [key]
      exact hb𝔮 hbO
    · intro c hc
      have hcO : e.symm (c : K) ∈ O := (memO' _).mp hc
      have hcC : e.symm (c : K) ∈ C := hCbwd _ c.2
      have heC : e ((⟨e.symm (c : K), hcC⟩ : ↥C) : K) ∈ C := by
        show e (e.symm (c : K)) ∈ C
        rw [e.apply_symm_apply]; exact c.2
      have h1 := hpp' ⟨e.symm (c : K), hcC⟩ heC
      have key1 : (⟨e ((⟨e.symm (c : K), hcC⟩ : ↥C) : K), heC⟩ : ↥C) = c :=
        Subtype.ext (e.apply_symm_apply _)
      rw [key1] at h1
      rw [← h1, hc𝔮 ⟨e.symm (c : K), hcC⟩ hcO, Ideal.mem_comap]
      have key2 : ψ.symm ⟨(c : K), hc⟩ = ⟨((⟨e.symm (c : K), hcC⟩ : ↥C) : K), hcO⟩ := Subtype.ext rfl
      rw [key2]

end EndsPerm

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
                (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))
    (O : Subring ↥K)
    (hO : ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K) (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
    (hτW : ∀ f : ↥K, f ∈ W ↔ τ f ∈ W)
    :
      ∃ O' : Subring ↥K,
        (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O' ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O')) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O')) ∧
        (∀ f : ↥K, f ∈ O ↔ τ f ∈ O') ∧
        (∀ 𝔭 𝔭' : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) → (𝔭'.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭' ∧ 𝔭' ≤ y ∧ 𝔭' ≠ y) → (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮)) →
          (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : τ (c : ↥K) ∈ chartAlgFin A (↥K) j), c ∈ 𝔭 ↔ (⟨τ (c : ↥K), hc⟩ : ↥(chartAlgFin A (↥K) j)) ∈ 𝔭') →
          (∃ 𝔮 : Ideal ↥O', 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O', (⟨algebraMap A ↥K ϖ, h⟩ : ↥O') ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O') ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O'),
              c ∈ 𝔭' ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O') ∈ 𝔮))) := by

  have hW := hW₁
  obtain ⟨-, hfin, -, -, -, -, -⟩ := hW

  obtain ⟨hU, hM, hI⟩ := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have hE := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have hmul : ∀ γ δ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → δ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') δ⁻¹ K σ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') (γ * δ)⁻¹ K (τ * σ) := by
    intro γ δ hγ hδ τ σ hτ hσ
    have h := hM γ⁻¹ δ⁻¹ (inv_mem hγ) (inv_mem hδ) τ σ hτ hσ
    rw [← mul_inv_rev] at h
    exact h
  have hone : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') (1 : SL(2, ℤ))⁻¹ K 1 := by
    rw [inv_one]; exact hI 1 (one_mem _) (one_mem _)
  have huniq : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ τ' : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ' → τ = τ' :=
    fun γ hγ τ τ' h h' => hU γ⁻¹ (inv_mem hγ) τ τ' h h'
  have hinv : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹⁻¹ K τ⁻¹ := by
    intro γ hγ τ hτ
    obtain ⟨τ', hτ'⟩ := hE γ⁻¹ (inv_mem hγ)
    have h1 := hmul γ⁻¹ γ (inv_mem hγ) hγ τ' τ hτ' hτ
    rw [inv_mul_cancel] at h1
    have h2 : τ' * τ = 1 := huniq 1 (one_mem _) _ _ h1 hone
    have h3 : τ' = τ⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [← h3]; exact hτ'

  have hK1 := ModularCurve.FullLevel.AuxLevel.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y
    W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  obtain ⟨-, hii, -⟩ := hK1

  have hτ' := hinv γ hγ τ hτ
  have hfinτ : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j := hfin γ hγ τ hτ
  have hfinτ' : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ⁻¹ a ∈ chartAlgFin A (↥K) j :=
    hfin γ⁻¹ (inv_mem hγ) τ⁻¹ hτ'
  have hC : ∀ x : ↥K, x ∈ chartAlgFin A (↥K) j ↔ τ x ∈ chartAlgFin A (↥K) j := by
    intro x
    refine ⟨hfinτ x, fun h => ?_⟩
    have h2 := hfinτ' (τ x) h
    have h3 : τ⁻¹ (τ x) = x := τ.symm_apply_apply x
    rwa [h3] at h2
  have hϖτ : τ (algebraMap A ↥K ϖ) = algebraMap A ↥K ϖ := by
    rw [IsScalarTower.algebraMap_apply A L ↥K ϖ]; exact τ.commutes _
  exact EndsPerm.transport (chartAlgFin A (↥K) j) J y B ϖ W τ.toRingEquiv ⇑τ (fun _ => rfl) hC
    (hii γ hγ τ hτ) (hEQ.2.1 γ hγ τ hτ) hτW hR3.2.2.2.1 hϖτ O hO

end S_ModularCurve_FullLevel_AuxLevel_exists_isEnd_blowupChart_map_of_isLevelAutAt_of_mem_valuationSubring_iff_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isEnd_blowupChart_map_of_isLevelAutAt_of_mem_valuationSubring_iff_of_drinfeldChartWitness_linked (solution)
