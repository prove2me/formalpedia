-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1e65e55f-87a1-5626-8f60-c35d4d015069

import Mathlib
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual

universe u v w w'

set_option autoImplicit false

open scoped TensorProduct
open Function

namespace R4K4aLift

section Reduction

variable {𝓞 : Type u} [CommRing 𝓞] (k : Type v) [Field k] [Algebra 𝓞 k]
variable {X : Type w} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]

private noncomputable def red (x : X →ₐ[𝓞] Y) : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.map (AlgHom.id k k) x

variable {k}

@[scoped simp] private theorem red_tmul (x : X →ₐ[𝓞] Y) (c : k) (r : X) : red k x (c ⊗ₜ[𝓞] r) = c ⊗ₜ[𝓞] x r := by
  rw [red, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

private theorem sub_mem_span_of_red_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {x x' : X →ₐ[𝓞] Y} (h : red k x = red k x') (r : X) :
    x r - x' r ∈ Ideal.span {(p : Y)} := by
  rw [← Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y) hk hker, RingHom.mem_ker,
    Deformation.SpecialFibre.reduction_apply, TensorProduct.tmul_sub, ← red_tmul, ← red_tmul, h, sub_self]

end Reduction

section TwoVariables

variable {𝓞 : Type u} [CommRing 𝓞] (k : Type v) [Field k] [Algebra 𝓞 k]
variable (ℛ : Type w) [CommRing ℛ] [Algebra 𝓞 ℛ]

private noncomputable def redLeft : ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  (Algebra.TensorProduct.includeLeft (S := 𝓞)).comp Algebra.TensorProduct.includeRight

private noncomputable def redRight : ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  ((Algebra.TensorProduct.includeRight :
        k ⊗[𝓞] ℛ →ₐ[k] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)).restrictScalars 𝓞).comp
      Algebra.TensorProduct.includeRight

private noncomputable def pi2 : ℛ ⊗[𝓞] ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  Algebra.TensorProduct.lift (redLeft k ℛ) (redRight k ℛ)
    (fun _ _ => Commute.all (S := (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)) _ _)

private noncomputable def theta : (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) →ₐ[k] k ⊗[𝓞] (ℛ ⊗[𝓞] ℛ) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.map (AlgHom.id k k)
      (Algebra.TensorProduct.includeLeft : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ))
    ((Algebra.TensorProduct.map (AlgHom.id k k)
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ)).restrictScalars k)
    (fun _ _ => Commute.all (S := k ⊗[𝓞] (ℛ ⊗[𝓞] ℛ)) _ _)

variable {k ℛ}

private theorem pi2_tmul (r s : ℛ) :
    pi2 k ℛ (r ⊗ₜ[𝓞] s) = ((1 : k) ⊗ₜ[𝓞] r) ⊗ₜ[k] ((1 : k) ⊗ₜ[𝓞] s) := by
  rw [pi2, Algebra.TensorProduct.lift_tmul]
  change (((1 : k) ⊗ₜ[𝓞] r) ⊗ₜ[k] (1 : k ⊗[𝓞] ℛ)) * ((1 : k ⊗[𝓞] ℛ) ⊗ₜ[k] ((1 : k) ⊗ₜ[𝓞] s)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem theta_pi2 (z : ℛ ⊗[𝓞] ℛ) : theta k ℛ (pi2 k ℛ z) = (1 : k) ⊗ₜ[𝓞] z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, TensorProduct.tmul_zero]
  | tmul r s =>
    rw [pi2_tmul, theta, Algebra.TensorProduct.lift_tmul]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]

private theorem ker_pi2 (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (pi2 (𝓞 := 𝓞) k ℛ).toRingHom = Ideal.span {(p : ℛ ⊗[𝓞] ℛ)} := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have h1 : (1 : k) ⊗ₜ[𝓞] z = 0 := by
      rw [← theta_pi2 z]
      change theta k ℛ ((pi2 k ℛ).toRingHom z) = 0
      rw [hz, map_zero]
    have : z ∈ RingHom.ker (Deformation.SpecialFibre.reduction 𝓞 k (ℛ ⊗[𝓞] ℛ)) := by
      rw [RingHom.mem_ker, Deformation.SpecialFibre.reduction_apply, h1]
    rwa [Deformation.SpecialFibre.ker_reduction_eq_span hk hker] at this
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    have h := Deformation.SpecialFibre.natCast_eq_zero (ℛ := ℛ) hk hker
    rw [← map_natCast (algebraMap (k ⊗[𝓞] ℛ) ((k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ))), h, map_zero]

private theorem sub_mem_span_of_pi2_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) {a b : ℛ ⊗[𝓞] ℛ}
    (h : pi2 k ℛ a = pi2 k ℛ b) : a - b ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)} := by
  rw [← ker_pi2 hk hker, RingHom.mem_ker, map_sub]
  change pi2 k ℛ a - pi2 k ℛ b = 0
  rw [h, sub_self]

end TwoVariables

section Comul

variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [Field k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ]

private theorem comul_one_tmul (r : ℛ) :
    Coalgebra.comul (R := k) ((1 : k) ⊗ₜ[𝓞] r) = pi2 k ℛ (Coalgebra.comul (R := 𝓞) r) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply k 1]
  induction Coalgebra.comul (R := 𝓞) r using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul x y =>
    rw [pi2_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

private theorem counit_one_tmul (r : ℛ) :
    Coalgebra.counit (R := k) ((1 : k) ⊗ₜ[𝓞] r) = algebraMap 𝓞 k (Coalgebra.counit (R := 𝓞) r) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_eq_smul_one]

end Comul

section Lift

variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [Field k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ]
variable {ℛ' : Type w'} [CommRing ℛ'] [Bialgebra 𝓞 ℛ']

private theorem apply_one_tmul_of_red_eq {g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ} {f₀ : ℛ' →ₐ[𝓞] ℛ}
    (h : red k f₀ = g) (r : ℛ') : g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r := by
  rw [← h, red_tmul]

private theorem pi2_map_map (g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) (w : ℛ' ⊗[𝓞] ℛ') :
    pi2 k ℛ (Algebra.TensorProduct.map f₀ f₀ w) =
      TensorProduct.map g.toLinearMap g.toLinearMap (pi2 k ℛ' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, pi2_tmul, pi2_tmul, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hg, hg]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem counitAlgHom_comp_eq {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    (Bialgebra.counitAlgHom 𝓞 ℛ).comp f₀ = Bialgebra.counitAlgHom 𝓞 ℛ' := by
  refine hinj _ _ fun r => ?_
  rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
  change algebraMap 𝓞 k (Coalgebra.counit (R := 𝓞) (f₀ r)) =
    algebraMap 𝓞 k (Coalgebra.counit (R := 𝓞) r)
  rw [← counit_one_tmul (k := k), ← counit_one_tmul (k := k), ← hg,
    CoalgHomClass.counit_comp_apply]

private theorem map_comp_comulAlgHom_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    (Algebra.TensorProduct.map f₀ f₀).comp (Bialgebra.comulAlgHom 𝓞 ℛ') =
      (Bialgebra.comulAlgHom 𝓞 ℛ).comp f₀ := by
  refine hinj _ _ fun r => sub_mem_span_of_pi2_eq (k := k) hk hker ?_
  change pi2 k ℛ (Algebra.TensorProduct.map f₀ f₀ (Coalgebra.comul (R := 𝓞) r)) =
    pi2 k ℛ (Coalgebra.comul (R := 𝓞) (f₀ r))
  rw [pi2_map_map (g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) f₀ hg, ← comul_one_tmul, ← comul_one_tmul, ← hg]
  exact (CoalgHomClass.map_comp_comul_apply g _)

private noncomputable def bialgHomOfLift (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj₁ : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (hinj₂ : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) : ℛ' →ₐc[𝓞] ℛ :=
  BialgHom.ofAlgHom f₀ (counitAlgHom_comp_eq hker hinj₁ g f₀ hg)
    (map_comp_comulAlgHom_eq hk hker hinj₂ g f₀ hg)

private theorem bialgHomOfLift_toAlgHom (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj₁ : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (hinj₂ : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    (bialgHomOfLift hk hker hinj₁ hinj₂ g f₀ hg : ℛ' →ₐ[𝓞] ℛ) = f₀ :=
  AlgHom.ext fun _ => rfl

end Lift

end R4K4aLift
p2m_reactivate "P2MW.S_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual.R4K4aLift"

theorem solution
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : O))
    (k : Type v) [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra O ℛ] [Module.Finite O ℛ] [Module.Free O ℛ]
    (H : Type w') [CommRing H] [HopfAlgebra O H] [Coalgebra.IsCocomm O H]
    [Module.Finite O H] [Module.Free O H] (hrank : ∃ a : ℕ, Module.finrank O H = p ^ a)
    (hunip : IsLocalRing (CartierDual k (TensorProduct O k H)))
    (ψ : TensorProduct O k H →ₐc[k] TensorProduct O k ℛ)
    (x : H →ₐ[O] ℛ)
    (hx : Algebra.TensorProduct.map (AlgHom.id k k) x =
      (ψ : TensorProduct O k H →ₐ[k] TensorProduct O k ℛ)) :
    ∃ Φ : H →ₐc[O] ℛ, (Φ : H →ₐ[O] ℛ) = x := by
  have hinj₁ : ∀ (y y' : H →ₐ[O] O), (∀ h : H, y h - y' h ∈ Ideal.span {(p : O)}) → y = y' :=
    fun y y' hyy' =>
      HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual O p hunif k hk hker H
        hrank hunip O y y' hyy'
  have hinj₂ : ∀ (y y' : H →ₐ[O] TensorProduct O ℛ ℛ),
      (∀ h : H, y h - y' h ∈ Ideal.span {(p : TensorProduct O ℛ ℛ)}) → y = y' :=
    fun y y' hyy' =>
      HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual O p hunif k hk hker H
        hrank hunip (TensorProduct O ℛ ℛ) y y' hyy'
  have hg : ∀ h : H, ψ ((1 : k) ⊗ₜ[O] h) = (1 : k) ⊗ₜ[O] x h := fun h => by
    change (ψ : TensorProduct O k H →ₐ[k] TensorProduct O k ℛ) ((1 : k) ⊗ₜ[O] h) = _
    rw [← hx]
    rfl
  exact ⟨R4K4aLift.bialgHomOfLift hk hker hinj₁ hinj₂ ψ x hg,
    R4K4aLift.bialgHomOfLift_toAlgHom hk hker hinj₁ hinj₂ ψ x hg⟩

end S_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual (solution)
