-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.comb_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:33:04.726034+00:00
-- url     : https://prove2.me/submissions/49147f2e-8747-4779-a5d3-fabebfb59f8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_eq
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_nonneg
import Theorems.Thm_GlobalTheory_Reg_Transfer_nval_eq_vr
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_mul
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_pow
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_inv
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_alg
import Theorems.Thm_GlobalTheory_Reg_Transfer_chval_fin_zpow
import Theorems.Thm_P2M_GlobalTheory_Reg_Transfer_vV_zero__d1cc3821e421
import Theorems.Thm_GlobalTheory_Reg_Transfer_regular_at_centre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (ϖ : O) (eO : ℕ) (heO : 0 < eO)
    (fw fe : FractionRing A) (hfw0 : fw ≠ 0) (x : A) (hx : x ≠ 0)
    (ye : A) (hye : ye ≠ 0) (te : ℕ)
    (hfe : fe * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ te) = algebraMap A (FractionRing A) ye)
    (yw : A) (tw : ℕ)
    (hfw : fw⁻¹ * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw) = algebraMap A (FractionRing A) yw)
    (nu0 c' : ℝ) (N : ℕ) (Aexp : ℤ) (B : ℕ) (hA : (eO : ℝ) * N * nu0 ≤ Aexp) (hB : (N : ℝ) * c' ≤ B)
    (halg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V), φ x ≠ 0 → ∃ (e : ℕ) (W T : EReal), 0 < e ∧
        vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * (eO : ℤ) = e ∧
        ChV φ.toRingHom e fw W ∧ ChV φ.toRingHom e fe T ∧ 0 ≤ T ∧
        (T ≠ ⊤ → W ≤ (nu0 : EReal) + (c' : EReal) * T))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V] (φ : A →ₐ[O] V)
    (hφx : φ x ≠ 0) (hφϖ : algebraMap O V ϖ ≠ 0)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤)
    (e : ℕ) (w t : ℝ) (hW : ChV φ.toRingHom e fw (w : EReal)) (hT : ChV φ.toRingHom e fe (t : EReal)) :
    (N : ℝ) * w ≤ Aexp * vr e (algebraMap O V ϖ) + B * t := by
  classical
  set ϖA : FractionRing A := algebraMap A (FractionRing A) (algebraMap O A ϖ)
  set g : FractionRing A := ϖA ^ Aexp * fe ^ B * (fw ^ N)⁻¹

  have hgval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      (φ : A →ₐ[O] V) (e : ℕ) (w t : ℝ), algebraMap O V ϖ ≠ 0 → ChV φ.toRingHom e fw (w : EReal) →
      ChV φ.toRingHom e fe (t : EReal) →
      ChV φ.toRingHom e g (((Aexp : ℝ) * vr e (algebraMap O V ϖ) + B * t + -((N : ℝ) * w) : ℝ) : EReal) := by
    intro V _ _ _ _ φ e w t hϖ hW hT
    have h1 : φ.toRingHom (algebraMap O A ϖ) ≠ 0 := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact hϖ
    have hϖv := chval_fin_alg φ.toRingHom e (algebraMap O A ϖ) h1
    rw [show φ.toRingHom (algebraMap O A ϖ) = algebraMap O V ϖ by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]] at hϖv
    exact chval_fin_mul _ _ (chval_fin_mul _ _ (chval_fin_zpow _ _ hϖv Aexp) (chval_fin_pow _ _ hT B))
      (chval_fin_inv _ _ (chval_fin_pow _ _ hW N))
  have hyeK : algebraMap A (FractionRing A) ye ≠ 0 := fun h => hye (IsFractionRing.injective A _ (by rw [h, map_zero]))
  obtain ⟨a, s, hs, hgs⟩ := regular_at_centre (O := O) g (x * ye) (mul_ne_zero hx hye)
    (fun V _ _ _ _ _ φ' hφ' => by
      rw [map_mul] at hφ'
      have hφ'x : φ' x ≠ 0 := left_ne_zero_of_mul hφ'
      have hφ'y : φ' ye ≠ 0 := right_ne_zero_of_mul hφ'
      obtain ⟨e', W', T', he', hϖ', hW', hT', hT0, hb⟩ := halg V φ' hφ'x
      have hϖ0 : algebraMap O V ϖ ≠ 0 := by
        intro h0
        rw [h0, map_zero, vV_zero', zero_mul] at hϖ'
        omega
      have hP : ∀ k : ℕ, φ' ((algebraMap O A ϖ * x) ^ k) ≠ 0 := by
        intro k
        rw [map_pow, map_mul, AlgHom.commutes]
        exact pow_ne_zero _ (mul_ne_zero hϖ0 hφ'x)

      have hTe := chval_eq φ'.toRingHom e' fe T' hT' ye _ hfe (hP te)
      have hTf : T' = ((vr e' (φ' ye) - vr e' (φ' ((algebraMap O A ϖ * x) ^ te)) : ℝ) : EReal) := by
        rw [hTe, EReal.coe_sub, ← nval_eq_vr e' hφ'y, ← nval_eq_vr e' (hP te)]
        rfl

      obtain ⟨xw, sw, hsw, hfws, hWv⟩ := hW'
      have hrel : fw * algebraMap A (FractionRing A) yw = algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw) := by
        rw [← hfw]; field_simp
      have hxy : xw * yw = sw * (algebraMap O A ϖ * x) ^ tw := by
        apply IsFractionRing.injective A (FractionRing A)
        rw [map_mul, map_mul, ← hfws, ← hrel]; ring
      have hxw : φ' xw ≠ 0 := by
        intro h0
        have := congrArg φ' hxy
        rw [map_mul, map_mul, h0, zero_mul] at this
        exact mul_ne_zero hsw (hP tw) this.symm
      have hWf : W' = ((vr e' (φ' xw) - vr e' (φ' sw) : ℝ) : EReal) := by
        rw [hWv, EReal.coe_sub]
        exact congrArg₂ (· - ·) (nval_eq_vr e' hxw) (nval_eq_vr e' hsw)
      set w' := vr e' (φ' xw) - vr e' (φ' sw)
      set t' := vr e' (φ' ye) - vr e' (φ' ((algebraMap O A ϖ * x) ^ te))
      have hWc : ChV φ'.toRingHom e' fw (w' : EReal) := hWf ▸ ⟨xw, sw, hsw, hfws, hWv⟩
      have hTc : ChV φ'.toRingHom e' fe (t' : EReal) := hTf ▸ hT'
      have ht0 : 0 ≤ t' := by rw [hTf] at hT0; exact_mod_cast hT0
      have hwb : w' ≤ nu0 + c' * t' := by
        have := hb (by rw [hTf]; exact EReal.coe_ne_top _)
        rw [hWf, hTf, ← EReal.coe_mul, ← EReal.coe_add] at this
        exact_mod_cast this
      have hκ : vr e' (algebraMap O V ϖ) * eO = 1 := by
        unfold vr
        have hv : ((vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) : ℤ) : ℝ) * eO = e' := by
          exact_mod_cast hϖ'
        have he'r : (0 : ℝ) < e' := by exact_mod_cast he'
        field_simp
        linarith
      refine ⟨e', _, he', hgval V φ' e' w' t' hϖ0 hWc hTc, ?_⟩
      have heOr : (0 : ℝ) < eO := by exact_mod_cast heO
      have h1 : (N : ℝ) * nu0 ≤ Aexp * vr e' (algebraMap O V ϖ) := by
        have hv1 : vr e' (algebraMap O V ϖ) = 1 / eO := by
          rw [eq_div_iff (ne_of_gt heOr)]; exact hκ
        have : (Aexp : ℝ) * vr e' (algebraMap O V ϖ) = Aexp / eO := by
          rw [hv1, mul_one_div]
        rw [this, le_div_iff₀ heOr]
        linarith
      have h2 : (N : ℝ) * c' * t' ≤ B * t' := mul_le_mul_of_nonneg_right hB ht0
      have h3 : (N : ℝ) * w' ≤ N * (nu0 + c' * t') := mul_le_mul_of_nonneg_left hwb (Nat.cast_nonneg N)
      exact EReal.coe_nonneg.2 (by nlinarith))
    ((maximalIdeal V).comap φ.toRingHom) hqq
  have hval := hgval V φ e w t hφϖ hW hT
  have := chval_nonneg φ.toRingHom e g _ hval a s hgs hs
  have h0 := EReal.coe_nonneg.1 this
  linarith
end GlobalTheory.Reg.Transfer
