-- Prove2me | solution 1 for GlobalTheory.FlatDescent.hilbert90_local_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:31:02.551314+00:00
-- url     : https://prove2.me/submissions/693ae898-3e47-4033-973f-0ababf7ba416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_Hilbert90LocalOfCocycleTensor
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FlatDescent_IsDescentDatum_bijective_extend
import Theorems.Thm_GlobalTheory_FlatDescent_IsDescentDatum_invertible_invariants
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.FlatDescent
namespace GlobalTheory.FlatDescent
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  intro R S _ _ _ _ _ _ c hc p hp
  classical
  let θ : S →ₗ[S] S ⊗[R] S := LinearMap.toSpanSingleton S (S ⊗[R] S) (c : S ⊗[R] S)
  have hθ : ∀ n, θ n = (n ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) := fun n => by
    simp [θ, Algebra.smul_def]

  let ψ : (S ⊗[R] S) ⊗[R] S →ₐ[R] S ⊗[R] S :=
    Algebra.TensorProduct.lift (S := R) (AlgHom.id R (S ⊗[R] S))
      (Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)
  have h1 : ∀ x, ψ (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x) = x := by
    intro x; simp [ψ, ← Algebra.TensorProduct.one_def]
  have h2 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
      (AlgHom.id R S) x) = (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
    | tmul a b => simp [ψ]
  have h3 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
      (AlgHom.id R S) x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [ψ]
  have hμ : Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = 1 := by
    have h := congrArg ψ hc
    rw [map_mul, h1, h2, h3] at h
    have h' : (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] (1 : S) :=
      (Units.mul_right_inj c).1 (h.trans (mul_one _).symm)
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) S h'
  have hact : ∀ x, act R S S x = Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp
  have hcounit : ∀ n, act R S S (θ n) = n := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', (act R S S).map_smul, hact, hμ, smul_eq_mul, mul_one]

  let e := (TensorProduct.assoc R S S S)
  have hL0 : ∀ (a b : S) (z : S ⊗[R] S), a ⊗ₜ[R] (b • z) =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (a ⊗ₜ[R] b) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) z) := by
    intro a b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, mul_add, smul_add, tmul_add]
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, e, TensorProduct.assoc_tmul, smul_tmul',
        smul_eq_mul]
  have hL : ∀ x : S ⊗[R] S, (θ.restrictScalars R).lTensor S x =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) (c : S ⊗[R] S)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_mul]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars]
      exact hL0 a b _
  have hR : ∀ x : S ⊗[R] S, (TensorProduct.mk R S S 1).lTensor S x =
      e (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
        (AlgHom.id R S) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [e]
  have hsmul : ∀ (g : S →ₗ[R] S ⊗[R] S) (n : S) (x : S ⊗[R] S),
      g.lTensor S (n • x) = n • g.lTensor S x := by
    intro g n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a b => simp [smul_tmul']
  have hcoassoc : ∀ n, (θ.restrictScalars R).lTensor S (θ n) = (TensorProduct.mk R S S 1).lTensor S (θ n) := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', hsmul, hsmul, hL, hR, hc]
  have hD : IsDescentDatum θ := ⟨hcounit, hcoassoc⟩
  haveI : Module.Invertible R (invariants θ) := hD.invertible_invariants

  obtain ⟨f, m, hfm⟩ : ∃ (f : Module.Dual R (invariants θ)) (m : invariants θ), f m ∉ p := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨T, hT⟩ := ((Module.Invertible.linearEquiv R (invariants θ)).symm 1).exists_finset
    have h1 : (1 : R) = ∑ i ∈ T, i.1 i.2 := by
      have := congrArg (Module.Invertible.linearEquiv R (invariants θ)) hT
      simpa [Module.Invertible.linearEquiv, map_sum] using this
    exact hp.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.sum_mem _ fun i _ => hcon i.1 i.2))
  have hcomm : ∀ x : invariants θ, f m • x = f x • m := by
    intro x
    have := congrArg (TensorProduct.lift ((LinearMap.lsmul R (invariants θ)).comp f))
      (Module.Invertible.tmul_comm (m₁ := m) (m₂ := x))
    simpa using this
  obtain ⟨y, hy⟩ := hD.bijective_extend.2 1
  have hspan : ∀ y : S ⊗[R] invariants θ,
      algebraMap R S (f m) * extend S (invariants θ) y ∈ Ideal.span {(m : S)} := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, mul_add]; exact Ideal.add_mem _ hx hy
    | tmul b x =>
      have hx : algebraMap R S (f m) * (x : S) = algebraMap R S (f x) * (m : S) := by
        have := congrArg Subtype.val (hcomm x)
        simpa [Algebra.smul_def] using this
      rw [extend_tmul, smul_eq_mul, mul_left_comm, hx, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hspan y)
  refine ⟨f m, hfm, m, s, 1, ?_, ?_⟩
  · rw [← hθ]; exact mem_invariants.1 m.2
  · rw [pow_one, mul_comm, hs, hy, mul_one]
end GlobalTheory.FlatDescent
