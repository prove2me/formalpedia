-- Prove2me | solution 1 for HopfAlgebra.signTwist_comul_coassoc_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/13801291-171c-55fc-ae0a-3825a02de0f5

import Mathlib
import Theorems.Thm_HopfAlgebra_antipode_antipode
import Theorems.Thm_HopfAlgebra_map_antipode_comul_of_isCocomm
import Theorems.Thm_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_signTwist_comul_coassoc_padicInt

open scoped TensorProduct

set_option maxHeartbeats 9600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Δ' : H →ₗ[ℤ_[p]] (H ⊗[ℤ_[p]] H) :=
      Coalgebra.comul + (Ring.inverse d₀ - 1) • ((TensorProduct.map Pm Pm).comp Coalgebra.comul)
    ↑(TensorProduct.assoc ℤ_[p] H H H) ∘ₗ LinearMap.rTensor H Δ' ∘ₗ Δ'
      = LinearMap.lTensor H Δ' ∘ₗ Δ' := by
  intro Pm Δ'
  let ι : H →ₗ[ℤ_[p]] H := HopfAlgebra.antipode ℤ_[p]
  let t : ℤ_[p] := Ring.inverse (2:ℤ_[p])
  let Q := TensorProduct.map Pm Pm
  let Δ : H →ₗ[ℤ_[p]] H⊗[ℤ_[p]]H := Coalgebra.comul
  let D₁ : ℤ_[p] := Ring.inverse d₀ - 1
  let A := (TensorProduct.assoc ℤ_[p] H H H).toLinearMap
  have hΔ'exp : Δ' = Δ + D₁ • (Q.comp Δ) := rfl
  have hold : A ∘ₗ LinearMap.rTensor H Δ ∘ₗ Δ = LinearMap.lTensor H Δ ∘ₗ Δ :=
    Coalgebra.coassoc

  have hι2 : ∀ a : H, ι (ι a) = a := fun a => HopfAlgebra.antipode_antipode a
  have hιιΔ : ∀ a : H, (TensorProduct.map ι ι) (Δ a) = Δ (ι a) :=
    fun a => HopfAlgebra.map_antipode_comul_of_isCocomm hcocomm a
  have hPmι_a : ∀ a : H, Pm (ι a) = -Pm a := fun a => by
    show t • (ι a - ι (ι a)) = -(t • (a - ι a))
    rw [hι2, ← smul_neg, neg_sub]

  have hQιι : ∀ X, Q ((TensorProduct.map ι ι) X) = Q X := fun X => by
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [Q, TensorProduct.map_tmul, hPmι_a, neg_neg,
        TensorProduct.neg_tmul, TensorProduct.tmul_neg]
    | add x y hx hy => simp only [map_add, hx, hy]

  have hQΔPm : ∀ a : H, Q (Δ (Pm a)) = 0 := fun a => by
    have : Δ (Pm a) = t • (Δ a - (TensorProduct.map ι ι) (Δ a)) := by
      show Δ (t • (a - ι a)) = _
      rw [Δ.map_smul, map_sub, hιιΔ]
    rw [this, Q.map_smul, map_sub, hQιι, sub_self, smul_zero]

  have hrQΔQ : ∀ X, (LinearMap.rTensor H (Q.comp Δ)) (Q X) = 0 := fun X => by
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp only [Q, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        LinearMap.comp_apply, hQΔPm, TensorProduct.zero_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have hlQΔQ : ∀ X, (LinearMap.lTensor H (Q.comp Δ)) (Q X) = 0 := fun X => by
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp only [Q, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
        LinearMap.comp_apply, hQΔPm, TensorProduct.tmul_zero]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]

  have hrTadd : ∀ (f g : H →ₗ[ℤ_[p]] H⊗[ℤ_[p]]H),
      LinearMap.rTensor H (f + g) = LinearMap.rTensor H f + LinearMap.rTensor H g := by
    intro f g; ext x y; simp [LinearMap.rTensor_tmul]
  have hrTsmul : ∀ (c : ℤ_[p]) (f : H →ₗ[ℤ_[p]] H⊗[ℤ_[p]]H),
      LinearMap.rTensor H (c • f) = c • LinearMap.rTensor H f := by
    intro c f; ext x y; simp [LinearMap.rTensor_tmul]
  have hlTadd : ∀ (f g : H →ₗ[ℤ_[p]] H⊗[ℤ_[p]]H),
      LinearMap.lTensor H (f + g) = LinearMap.lTensor H f + LinearMap.lTensor H g := by
    intro f g; ext x y; simp [LinearMap.lTensor_tmul]
  have hlTsmul : ∀ (c : ℤ_[p]) (f : H →ₗ[ℤ_[p]] H⊗[ℤ_[p]]H),
      LinearMap.lTensor H (c • f) = c • LinearMap.lTensor H f := by
    intro c f; ext x y; simp [LinearMap.lTensor_tmul]

  have hI1 : ∀ a : H,
      A ((LinearMap.rTensor H (Q.comp Δ)) (Δ a)) + A ((LinearMap.rTensor H Δ) (Q (Δ a)))
      = (LinearMap.lTensor H (Q.comp Δ)) (Δ a) + (LinearMap.lTensor H Δ) (Q (Δ a)) :=
    HopfAlgebra.signTwist_coassoc_linearTerm_padicInt p hp2 d₀ hd₀ H hcocomm

  rw [hΔ'exp, hrTadd, hrTsmul, hlTadd, hlTsmul]
  ext a
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    LinearMap.map_smul]
  rw [show A ((LinearMap.rTensor H Δ) (Δ a)) = (LinearMap.lTensor H Δ) (Δ a) from
        LinearMap.congr_fun hold a,
      hrQΔQ (Δ a), hlQΔQ (Δ a), map_zero, smul_zero, smul_zero,
      add_zero, add_zero]

  rw [add_assoc, add_assoc, ← smul_add, ← smul_add, hI1 a]

end S_HopfAlgebra_signTwist_comul_coassoc_padicInt
end P2MW
export P2MW.S_HopfAlgebra_signTwist_comul_coassoc_padicInt (solution)
