-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d3d994c6-aadf-5f42-9ad6-e1ab6ad0c58a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace StabExc

noncomputable def twistHom {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    (B : Subalgebra A F) (W : ValuationSubring F) (hBW : ∀ f : F, f ∈ B → f ∈ W)
    (ρ : F → F) (hρB : ∀ f : F, f ∈ B → ρ f ∈ B)
    (hone : ρ 1 = 1) (hzero : ρ 0 = 0) (hmul : ∀ a b : F, ρ (a * b) = ρ a * ρ b)
    (hadd : ∀ a b : F, ρ (a + b) = ρ a + ρ b) : ↥B →+* ↥W where
  toFun b := ⟨ρ (b : F), hBW _ (hρB _ b.2)⟩
  map_one' := Subtype.ext (by simp [hone])
  map_mul' a b := Subtype.ext (by simp [hmul])
  map_zero' := Subtype.ext (by simp [hzero])
  map_add' a b := Subtype.ext (by simp [hadd])

@[scoped simp] theorem twistHom_apply_coe {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    (B : Subalgebra A F) (W : ValuationSubring F) (hBW : ∀ f : F, f ∈ B → f ∈ W)
    (ρ : F → F) (hρB : ∀ f : F, f ∈ B → ρ f ∈ B)
    (hone : ρ 1 = 1) (hzero : ρ 0 = 0) (hmul : ∀ a b : F, ρ (a * b) = ρ a * ρ b)
    (hadd : ∀ a b : F, ρ (a + b) = ρ a + ρ b) (b : ↥B) :
    ((twistHom B W hBW ρ hρB hone hzero hmul hadd b : ↥W) : F) = ρ (b : F) := rfl

theorem apply_mem_maximalIdeal_of_least {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    (C B : Subalgebra A F) (W : ValuationSubring F) (hBW : ∀ f : F, f ∈ B → f ∈ W) (hCB : C ≤ B)
    (y : Ideal ↥C) (ϖ : A) (hϖy : algebraMap A ↥C ϖ ∈ y)
    (hcen : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : F) ∈ W, (⟨(b : F), hb⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
      (∀ b : ↥C, (⟨(b : F), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : F), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ Q)
    (ρ : F → F) (hρC : ∀ a : F, a ∈ C → ρ a ∈ C) (hρB : ∀ f : F, f ∈ B → ρ f ∈ B)
    (hone : ρ 1 = 1) (hzero : ρ 0 = 0) (hmul : ∀ a b : F, ρ (a * b) = ρ a * ρ b)
    (hadd : ∀ a b : F, ρ (a + b) = ρ a + ρ b)
    (hfix : ∀ (b : ↥C) (hb : ρ (b : F) ∈ C), b ∈ y ↔ (⟨ρ (b : F), hb⟩ : ↥C) ∈ y) :
    ∀ (b : ↥B), (⟨(b : F), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W →
      ∀ hb' : ρ (b : F) ∈ W, (⟨ρ (b : F), hb'⟩ : ↥W) ∈ maximalIdeal ↥W := by
  classical
  set φ : ↥B →+* ↥W := twistHom B W hBW ρ hρB hone hzero hmul hadd with hφ
  set Q : Ideal ↥B := (maximalIdeal ↥W).comap φ with hQ
  have hQprime : Q.IsPrime := Ideal.comap_isPrime φ (maximalIdeal ↥W)

  have hmemQ : ∀ b : ↥B, b ∈ Q ↔
      (⟨ρ (b : F), hBW _ (hρB _ b.2)⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro b
    rw [hQ, Ideal.mem_comap]
    rfl

  have hϖQ : algebraMap A ↥B ϖ ∈ Q := by
    rw [hmemQ]

    set c : ↥C := algebraMap A ↥C ϖ with hc
    have hcval : ((algebraMap A ↥B ϖ : ↥B) : F) = (c : F) := by
      simp [hc, Subalgebra.coe_algebraMap]
    have hρc : ρ (c : F) ∈ C := hρC _ c.2
    have hcy : (⟨ρ (c : F), hρc⟩ : ↥C) ∈ y := (hfix c hρc).mp hϖy
    obtain ⟨hb, hbm⟩ := (hcen ⟨ρ (c : F), hρc⟩).mp hcy
    have : (⟨ρ ((algebraMap A ↥B ϖ : ↥B) : F), hBW _ (hρB _ (algebraMap A ↥B ϖ).2)⟩ : ↥W) =
        ⟨ρ (c : F), hb⟩ := Subtype.ext (by simp [hcval])
    rw [this]
    exact hbm

  have hcontr : ∀ b : ↥C, (⟨(b : F), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y := by
    intro b
    rw [hmemQ]
    have hρb : ρ (b : F) ∈ C := hρC _ b.2
    have h1 := hcen ⟨ρ (b : F), hρb⟩
    have h2 := hfix b hρb
    constructor
    · intro hm
      exact h2.mpr (h1.mpr ⟨hBW _ (hρB _ (hCB b.2)), hm⟩)
    · intro hy
      obtain ⟨hb, hbm⟩ := h1.mp (h2.mp hy)
      exact hbm
  intro b hb hb'
  have hbQ : b ∈ Q := hleast Q hQprime hϖQ hcontr b hb
  rw [hmemQ] at hbQ
  exact hbQ

theorem apply_mem_of_mem {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    (B : Subalgebra A F) (W : ValuationSubring F) (hBW : ∀ f : F, f ∈ B → f ∈ W)
    (hloc : ∀ f : F, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : F), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : F) = (g : F))
    (ρ σ : F → F) (hρB : ∀ f : F, f ∈ B → ρ f ∈ B)
    (hmul : ∀ a b : F, ρ (a * b) = ρ a * ρ b) (hσρ : ∀ x : F, σ (ρ x) = x)
    (h4 : ∀ (b : ↥B), (⟨(b : F), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W →
      ∀ hb' : σ (b : F) ∈ W, (⟨σ (b : F), hb'⟩ : ↥W) ∈ maximalIdeal ↥W) :
    ∀ f : F, f ∈ W → ρ f ∈ W := by
  intro f hf
  obtain ⟨g, h, hh, hfh⟩ := (hloc f).mp hf
  refine (hloc (ρ f)).mpr ⟨⟨ρ (g : F), hρB _ g.2⟩, ⟨ρ (h : F), hρB _ h.2⟩, ?_, ?_⟩
  · intro hm
    apply hh
    have := h4 ⟨ρ (h : F), hρB _ h.2⟩ hm (by rw [hσρ]; exact hBW _ h.2)
    have heq : (⟨σ (ρ (h : F)), by rw [hσρ]; exact hBW _ h.2⟩ : ↥W) = ⟨(h : F), hBW _ h.2⟩ :=
      Subtype.ext (hσρ _)
    rw [heq] at this
    exact this
  · show ρ f * ρ (h : F) = ρ (g : F)
    rw [← hmul, hfh]

end StabExc
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime.StabExc"

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
    (A : Type) [CommRing A] [Algebra A ↥K] (j : ↥K) (ϖ : A)
    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (B : Subalgebra A ↥K) (W : ValuationSubring ↥K)
    (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hloc : ∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K))

    (hcen : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
      ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W)

    (hpres : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)

    (hstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ f : ↥K, f ∈ B → τ f ∈ B)

    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
      (∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ Q) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
            b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
        ∀ f : ↥K, f ∈ W ↔ τ f ∈ W := by
  intro γ hγ τ hτ hfix f

  have hγ' : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ
  obtain ⟨σ, hσ⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq
      hℓM' L ξ hξ hι K hK γ⁻¹ hγ'
  obtain ⟨huniq, hmulLA, hone⟩ :=
    ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ
      hξ hι K hK
  have hσ' : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K σ := by
    simpa only [inv_inv] using hσ
  have h1 : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') (γ * γ⁻¹) K (τ * σ) :=
    hmulLA γ⁻¹ γ hγ' hγ τ σ hτ hσ'
  rw [mul_inv_cancel] at h1
  have h2 : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') 1 K 1 :=
    hone 1 (one_mem _) (one_mem _)
  have h3 : τ * σ = 1 := huniq 1 (one_mem _) (τ * σ) 1 h1 h2
  have h3' : σ * τ = 1 := by
    have hστinv : σ = τ⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
    rw [hστinv, inv_mul_cancel]
  have hτσ : ∀ x : ↥K, τ (σ x) = x := fun x => by
    have := congrArg (fun e : ↥K ≃ₐ[L] ↥K => e x) h3
    simpa [AlgEquiv.mul_apply] using this
  have hστ : ∀ x : ↥K, σ (τ x) = x := fun x => by
    have := congrArg (fun e : ↥K ≃ₐ[L] ↥K => e x) h3'
    simpa [AlgEquiv.mul_apply] using this

  have hσC : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → σ a ∈ chartAlgFin A (↥K) j := hpres γ⁻¹ hγ' σ hσ
  have hσB : ∀ f : ↥K, f ∈ B → σ f ∈ B := hstab γ⁻¹ hγ' σ hσ
  have hτC : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j := hpres γ hγ τ hτ
  have hτB : ∀ f : ↥K, f ∈ B → τ f ∈ B := hstab γ hγ τ hτ
  have hfixσ : ∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : σ (c : ↥K) ∈ chartAlgFin A (↥K) j),
      c ∈ y ↔ (⟨σ (c : ↥K), hc⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y := by
    intro c hc
    have hb : τ (σ (c : ↥K)) ∈ chartAlgFin A (↥K) j := by rw [hτσ]; exact c.2
    have h := hfix ⟨σ (c : ↥K), hc⟩ hb
    have heq : (⟨τ (σ (c : ↥K)), hb⟩ : ↥(chartAlgFin A (↥K) j)) = c := Subtype.ext (hτσ _)
    rw [heq] at h
    exact h.symm

  have h4τ := StabExc.apply_mem_maximalIdeal_of_least (chartAlgFin A (↥K) j) B W hBW hCB y ϖ hϖy hcen hleast
    (fun x => τ x) hτC hτB (map_one τ) (map_zero τ) (map_mul τ) (map_add τ) hfix
  have h4σ := StabExc.apply_mem_maximalIdeal_of_least (chartAlgFin A (↥K) j) B W hBW hCB y ϖ hϖy hcen hleast
    (fun x => σ x) hσC hσB (map_one σ) (map_zero σ) (map_mul σ) (map_add σ) hfixσ
  constructor
  · exact StabExc.apply_mem_of_mem B W hBW hloc (fun x => τ x) (fun x => σ x) hτB (map_mul τ) hστ h4σ f
  · intro hτf
    have := StabExc.apply_mem_of_mem B W hBW hloc (fun x => σ x) (fun x => τ x) hσB (map_mul σ) hτσ h4τ
      (τ f) hτf
    simpa [hστ] using this

end S_ModularCurve_FullLevel_AuxLevel_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_mem_iff_apply_mem_valuationSubring_of_isLevelAutAt_of_stabilizes_centre_of_least_prime (solution)
