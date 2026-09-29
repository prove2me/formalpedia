-- Prove2me | solution 1 for HopfAlgebra.signTwist_coassoc_linearTerm_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bb260162-7481-584b-8ad4-7bb55f5e827b

import Mathlib
import Theorems.Thm_HopfAlgebra_antipode_antipode
import Theorems.Thm_HopfAlgebra_map_antipode_comul_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt

open scoped TensorProduct

set_option maxHeartbeats 9600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Q := TensorProduct.map Pm Pm
    let Δ : H →ₗ[ℤ_[p]] H ⊗[ℤ_[p]] H := Coalgebra.comul
    let A := (TensorProduct.assoc ℤ_[p] H H H).toLinearMap
    ∀ a : H,
      A ((LinearMap.rTensor H (Q.comp Δ)) (Δ a)) + A ((LinearMap.rTensor H Δ) (Q (Δ a)))
      = (LinearMap.lTensor H (Q.comp Δ)) (Δ a) + (LinearMap.lTensor H Δ) (Q (Δ a)) := by
  intro Pm Q Δ A a
  let ι : H →ₗ[ℤ_[p]] H := HopfAlgebra.antipode ℤ_[p]
  let t : ℤ_[p] := Ring.inverse (2:ℤ_[p])
  let M : H⊗[ℤ_[p]]H →ₗ[ℤ_[p]] H⊗[ℤ_[p]]H := TensorProduct.map ι ι

  have hιιΔ : ∀ w : H, M (Δ w) = Δ (ι w) :=
    fun w => HopfAlgebra.map_antipode_comul_of_isCocomm hcocomm w
  have hΔPm : ∀ w : H, Δ (Pm w) = t • Δ w - t • M (Δ w) := fun w => by
    show Δ (t • (w - ι w)) = _
    rw [Δ.map_smul, map_sub, hιιΔ, smul_sub]
  have hcoassoc : A ((LinearMap.rTensor H Δ) (Δ a)) = (LinearMap.lTensor H Δ) (Δ a) :=
    LinearMap.congr_fun Coalgebra.coassoc a
  have hPm_unfold : ∀ w : H, Pm w = t • w - t • ι w := fun w => by
    show t • (w - ι w) = _; rw [smul_sub]

  have hAnat : ∀ (f g h : H →ₗ[ℤ_[p]] H) (Y : (H⊗[ℤ_[p]]H)⊗[ℤ_[p]]H),
      A ((TensorProduct.map (TensorProduct.map f g) h) Y)
        = (TensorProduct.map f (TensorProduct.map g h)) (A Y) := by
    intro f g h Y
    induction Y using TensorProduct.induction_on with
    | zero => simp
    | tmul W w =>
      induction W using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        simp only [A, TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
          TensorProduct.assoc_tmul]
      | add W₁ W₂ h₁ h₂ =>
        simp only [map_add, TensorProduct.add_tmul, h₁, h₂]
    | add Y₁ Y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

  have hso1 : ∀ (c:ℤ_[p]) (u:H) (V:H⊗[ℤ_[p]]H), (c•u) ⊗ₜ[ℤ_[p]] V = c • (u ⊗ₜ V) :=
    fun c u V => TensorProduct.smul_tmul' c u V
  have hso2 : ∀ (c:ℤ_[p]) (u:H) (v:H), (c•u) ⊗ₜ[ℤ_[p]] v = c • (u ⊗ₜ v) :=
    fun c u v => TensorProduct.smul_tmul' c u v
  have hsi1 : ∀ (c:ℤ_[p]) (u:H) (V:H⊗[ℤ_[p]]H), u ⊗ₜ[ℤ_[p]] (c•V) = c • (u ⊗ₜ V) :=
    fun c u V => (TensorProduct.tmul_smul c u V)
  have hsi2 : ∀ (c:ℤ_[p]) (u:H) (v:H), u ⊗ₜ[ℤ_[p]] (c•v) = c • (u ⊗ₜ v) :=
    fun c u v => (TensorProduct.tmul_smul c u v)

  let L : H⊗[ℤ_[p]](H⊗[ℤ_[p]]H) →ₗ[ℤ_[p]] H⊗[ℤ_[p]](H⊗[ℤ_[p]]H) :=
    TensorProduct.map Pm (LinearMap.rTensor H Pm)
      + (t • LinearMap.lTensor H (LinearMap.lTensor H Pm)
         - t • TensorProduct.map ι (TensorProduct.map ι Pm))
  let R : H⊗[ℤ_[p]](H⊗[ℤ_[p]]H) →ₗ[ℤ_[p]] H⊗[ℤ_[p]](H⊗[ℤ_[p]]H) :=
    LinearMap.lTensor H Q
      + (t • LinearMap.rTensor (H⊗[ℤ_[p]]H) Pm
         - t • TensorProduct.map Pm (TensorProduct.map ι ι))
  have hkey : L = R := by
    apply LinearMap.ext; intro X
    induction X using TensorProduct.induction_on with
    | zero => simp
    | add X₁ X₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul x YZ =>
      induction YZ using TensorProduct.induction_on with
      | zero => simp
      | add YZ₁ YZ₂ h₁ h₂ =>
        simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | tmul y z =>
        simp only [L, R, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Q]
        rw [hPm_unfold x, hPm_unfold y, hPm_unfold z]
        simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub, smul_sub,
          hso1, hso2, hsi1, hsi2, smul_smul]
        first
        | module
        | · ring_nf; abel
        | abel

  have hlTcomp : LinearMap.lTensor H (Q.comp Δ)
      = (LinearMap.lTensor H Q).comp (LinearMap.lTensor H Δ) := by
    first
    | exact LinearMap.lTensor_comp H Q Δ
    | exact LinearMap.lTensor_comp ..
    | · ext u v; simp [LinearMap.lTensor_tmul]
  have hrTcomp : LinearMap.rTensor H (Q.comp Δ)
      = (LinearMap.rTensor H Q).comp (LinearMap.rTensor H Δ) := by
    first
    | exact LinearMap.rTensor_comp H Q Δ
    | exact LinearMap.rTensor_comp ..
    | · ext u v; simp [LinearMap.rTensor_tmul]
  have hrTQ_eq : LinearMap.rTensor H Q
      = TensorProduct.map (TensorProduct.map Pm Pm) (LinearMap.id : H →ₗ[ℤ_[p]] H) := by
    first | rfl | · ext u v w; simp [TensorProduct.map_tmul, LinearMap.rTensor_tmul]
  have hmap_rT : TensorProduct.map Pm (TensorProduct.map Pm (LinearMap.id : H →ₗ[ℤ_[p]] H))
      = TensorProduct.map Pm (LinearMap.rTensor H Pm) := by
    first | rfl | · congr 1; first | rfl | · ext u v; simp [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  have hT1L : A ((LinearMap.rTensor H (Q.comp Δ)) (Δ a))
      = (TensorProduct.map Pm (LinearMap.rTensor H Pm)) ((LinearMap.lTensor H Δ) (Δ a)) := by
    rw [hrTcomp, LinearMap.comp_apply, hrTQ_eq, hAnat, hcoassoc, hmap_rT]
  have hT1R : (LinearMap.lTensor H (Q.comp Δ)) (Δ a)
      = (LinearMap.lTensor H Q) ((LinearMap.lTensor H Δ) (Δ a)) := by
    rw [hlTcomp, LinearMap.comp_apply]

  have hT2R : ∀ W : H⊗[ℤ_[p]]H, (LinearMap.lTensor H Δ) (Q W)
      = t • (LinearMap.rTensor (H⊗[ℤ_[p]]H) Pm) ((LinearMap.lTensor H Δ) W)
        - t • (TensorProduct.map Pm M) ((LinearMap.lTensor H Δ) W) := by
    intro W
    induction W using TensorProduct.induction_on with
    | zero => simp
    | add W₁ W₂ h₁ h₂ =>
      simp only [map_add, smul_add, h₁, h₂]; abel
    | tmul u v =>
      simp only [Q, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
        LinearMap.rTensor_tmul, hΔPm, TensorProduct.tmul_sub, hsi1]

  have hmap_lTlT : TensorProduct.map (LinearMap.id : H →ₗ[ℤ_[p]] H)
        (TensorProduct.map (LinearMap.id : H →ₗ[ℤ_[p]] H) Pm)
      = LinearMap.lTensor H (LinearMap.lTensor H Pm) := by
    first | rfl | · ext x y z; simp [TensorProduct.map_tmul, LinearMap.lTensor_tmul]
  have hT2L : ∀ W : H⊗[ℤ_[p]]H, A ((LinearMap.rTensor H Δ) (Q W))
      = t • (LinearMap.lTensor H (LinearMap.lTensor H Pm)) (A ((LinearMap.rTensor H Δ) W))
        - t • (TensorProduct.map ι (TensorProduct.map ι Pm)) (A ((LinearMap.rTensor H Δ) W)) := by
    intro W
    induction W using TensorProduct.induction_on with
    | zero => simp
    | add W₁ W₂ h₁ h₂ =>
      simp only [map_add, smul_add, h₁, h₂]; abel
    | tmul u v =>
      have hso3 : ∀ (c:ℤ_[p]) (U:H⊗[ℤ_[p]]H) (w:H), (c•U) ⊗ₜ[ℤ_[p]] w = c • (U ⊗ₜ w) :=
        fun c U w => TensorProduct.smul_tmul' c U w
      simp only [Q, TensorProduct.map_tmul, LinearMap.rTensor_tmul, hΔPm,
        TensorProduct.sub_tmul, hso3, map_sub, map_smul, smul_sub]
      congr 1
      · congr 1
        rw [show (Δ u) ⊗ₜ[ℤ_[p]] (Pm v)
              = (TensorProduct.map (TensorProduct.map LinearMap.id LinearMap.id) Pm) (Δ u ⊗ₜ v)
            from by simp [TensorProduct.map_tmul],
          hAnat, hmap_lTlT]
      · congr 1
        rw [show (M (Δ u)) ⊗ₜ[ℤ_[p]] (Pm v)
              = (TensorProduct.map (TensorProduct.map ι ι) Pm) (Δ u ⊗ₜ v)
            from by simp only [M, TensorProduct.map_tmul],
          hAnat]

  rw [hT1L, hT1R, hT2L (Δ a), hT2R (Δ a), hcoassoc]
  have := LinearMap.congr_fun hkey ((LinearMap.lTensor H Δ) (Δ a))
  simp only [L, R, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, M] at this
  first
  | exact this
  | · rw [add_sub_assoc, add_sub_assoc] at this; exact this
  | · convert this using 2 <;> (try rfl) <;> (try congr 1)
  | linarith [this]

end S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt
end P2MW
export P2MW.S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt (solution)
