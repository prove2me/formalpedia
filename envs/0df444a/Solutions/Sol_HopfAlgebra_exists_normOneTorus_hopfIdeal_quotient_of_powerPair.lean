-- Prove2me | solution 1 for HopfAlgebra.exists_normOneTorus_hopfIdeal_quotient_of_powerPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4ec503bc-640d-5970-b5a3-6ee4ea1b7747

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_normOneTorus_hopfIdeal_quotient_of_powerPair

set_option maxHeartbeats 24000000
open scoped TensorProduct

theorem solution
    (K : Type) [Field K] (c : K)
    (B₀ : Type) [CommRing B₀] [HopfAlgebra K B₀] (hcc₀ : Coalgebra.IsCocomm K B₀)
    (u₀ v₀ : B₀)
    (hgen₀ : Algebra.adjoin K {u₀, v₀} = ⊤)
    (hrel₀ : u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1)
    (hcu₀ : Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀))
    (hcv₀ : Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀)
    (P Q : B₀)
    (hrelPQ : P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1)
    (hcP : Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q))
    (hcQ : Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P)
    (hεP : Coalgebra.counit (R := K) P = 1)
    (hεQ : Coalgebra.counit (R := K) Q = 0) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A) (π : B₀ →ₐ[K] A),
        π u₀ = u' ∧ π v₀ = v' ∧ π P = 1 ∧ π Q = 0 ∧
        (∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 →
          ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g) ∧
        (Algebra.adjoin K {u', v'} = ⊤) ∧
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') := by
  classical

  set ε₀ : B₀ →ₐ[K] K := Bialgebra.counitAlgHom K B₀
  set Δ₀ : B₀ →ₐ[K] B₀ ⊗[K] B₀ := Bialgebra.comulAlgHom K B₀
  let I : Ideal B₀ := Ideal.span {P - 1, Q}
  have hP1I : P - 1 ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  have hQI : Q ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  let A := B₀ ⧸ I
  let π : B₀ →ₐ[K] A := Ideal.Quotient.mkₐ K I
  have hπsurj : Function.Surjective π := Ideal.Quotient.mkₐ_surjective K I
  have hkerI : ∀ x ∈ I, π x = 0 := fun x hx => by
    simp only [π, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hπP : π P = 1 := by
    have h := hkerI _ hP1I; rw [map_sub, map_one, sub_eq_zero] at h; exact h
  have hπQ : π Q = 0 := hkerI _ hQI

  have vanish_on_I : ∀ {C : Type} [CommRing C] [Algebra K C] (φ : B₀ →ₐ[K] C),
      φ (P - 1) = 0 → φ Q = 0 → ∀ x ∈ I, φ x = 0 := by
    intro C _ _ φ hφP hφQ
    have hsub : ({P - 1, Q} : Set B₀) ⊆ (RingHom.ker φ.toRingHom : Set B₀) := by
      rintro x (rfl | rfl)
      · simpa [RingHom.mem_ker] using hφP
      · simpa [RingHom.mem_ker] using hφQ
    intro x hx
    simpa [RingHom.mem_ker] using (Ideal.span_le.mpr hsub) hx

  set S₀ : B₀ →ₗ[K] B₀ := HopfAlgebra.antipode K
  have hSax : ∀ b : B₀,
      LinearMap.mul' K B₀ (S₀.rTensor B₀ (Δ₀ b)) = algebraMap K B₀ (ε₀ b) :=
    fun b => DFunLike.congr_fun (HopfAlgebra.mul_antipode_rTensor_comul (R := K) (A := B₀)) b
  have hSaxL : ∀ b : B₀,
      LinearMap.mul' K B₀ (S₀.lTensor B₀ (Δ₀ b)) = algebraMap K B₀ (ε₀ b) :=
    fun b => DFunLike.congr_fun (HopfAlgebra.mul_antipode_lTensor_comul (R := K) (A := B₀)) b
  have hS1 : S₀ 1 = 1 := by
    have h := hSax 1
    simp only [map_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul,
      LinearMap.mul'_apply, mul_one] at h
    exact h
  have hSeq1 : S₀ P * P + algebraMap K B₀ c * (S₀ Q * Q) = 1 := by
    have h := hSax P
    rw [show Δ₀ P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q) from hcP] at h
    simp only [map_add, map_smul, LinearMap.rTensor_tmul, LinearMap.mul'_apply] at h
    rw [show (ε₀ P : K) = 1 from hεP, map_one, Algebra.smul_def] at h
    exact h
  have hSeq2 : S₀ P * Q + S₀ Q * P = 0 := by
    have h := hSax Q
    rw [show Δ₀ Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P from hcQ] at h
    simp only [map_add, LinearMap.rTensor_tmul, LinearMap.mul'_apply] at h
    rw [show (ε₀ Q : K) = 0 from hεQ, map_zero] at h
    exact h
  have hSP : S₀ P = P := by
    have key : S₀ P * (P ^ 2 - algebraMap K B₀ c * Q ^ 2) = P := by
      linear_combination P * hSeq1 - algebraMap K B₀ c * Q * hSeq2
    rwa [hrelPQ, mul_one] at key
  have hSQ : S₀ Q = -Q := by
    have key : S₀ Q * (P ^ 2 - algebraMap K B₀ c * Q ^ 2) = -Q := by
      linear_combination -(Q * hSeq1) + P * hSeq2
    rwa [hrelPQ, mul_one] at key

  let S₀AH : B₀ →ₐ[K] B₀ :=
    { toFun := S₀
      map_one' := hS1
      map_mul' := fun x y =>
        (HopfAlgebra.antipode_mul (R := K) (A := B₀) x y).trans (mul_comm _ _)
      map_zero' := S₀.map_zero
      map_add' := S₀.map_add
      commutes' := fun r => by
        show S₀ ((algebraMap K B₀) r) = (algebraMap K B₀) r
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hS1] }
  have hS₀AH_eq : ∀ b, S₀AH b = S₀ b := fun _ => rfl

  have hεI : ∀ x ∈ I, ε₀ x = 0 := vanish_on_I ε₀
    (by rw [map_sub, map_one, show (ε₀ P : K) = 1 from hεP]; ring)
    (show (ε₀ Q : K) = 0 from hεQ)
  let εA : A →ₐ[K] K := Ideal.Quotient.liftₐ I ε₀ hεI
  have hεAπ : ∀ b, εA (π b) = ε₀ b := fun b => rfl
  have hεAπ' : εA.comp π = ε₀ := AlgHom.ext hεAπ

  let ππ : B₀ ⊗[K] B₀ →ₐ[K] A ⊗[K] A := Algebra.TensorProduct.map π π
  have hππ_tmul : ∀ x y : B₀, ππ (x ⊗ₜ[K] y) = π x ⊗ₜ[K] π y :=
    fun x y => Algebra.TensorProduct.map_tmul π π x y
  have hΔI : ∀ x ∈ I, (ππ.comp Δ₀) x = 0 := vanish_on_I (ππ.comp Δ₀)
    (by
      simp only [AlgHom.comp_apply, map_sub, map_one]
      rw [show Δ₀ P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q) from hcP]
      simp only [map_add, map_smul, hππ_tmul, hπP, hπQ, TensorProduct.zero_tmul,
        smul_zero, add_zero, Algebra.TensorProduct.one_def]; ring)
    (by
      simp only [AlgHom.comp_apply]
      rw [show Δ₀ Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P from hcQ]
      simp only [map_add, hππ_tmul, hπP, hπQ, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, add_zero])
  let ΔA : A →ₐ[K] A ⊗[K] A := Ideal.Quotient.liftₐ I (ππ.comp Δ₀) hΔI
  have hΔAπ : ∀ b, ΔA (π b) = ππ (Δ₀ b) := fun b => rfl
  have hΔAπ' : ΔA.comp π = ππ.comp Δ₀ := AlgHom.ext hΔAπ

  have algHom_surj_ext : ∀ {C : Type} [CommRing C] [Algebra K C]
      (φ ψ : A →ₐ[K] C), (∀ b, φ (π b) = ψ (π b)) → φ = ψ := by
    intro C _ _ φ ψ h
    exact AlgHom.ext fun a => by obtain ⟨b, rfl⟩ := hπsurj a; exact h b

  letI instBialgA : Bialgebra K A := Bialgebra.ofAlgHom ΔA εA
    (by

      have keyL : (Algebra.TensorProduct.map ΔA (AlgHom.id K A)).comp ππ
                = (Algebra.TensorProduct.map ππ π).comp
                  (Algebra.TensorProduct.map Δ₀ (AlgHom.id K B₀)) := by
        rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
          hΔAπ', AlgHom.comp_id, AlgHom.id_comp]
      have keyR : (Algebra.TensorProduct.map (AlgHom.id K A) ΔA).comp ππ
                = (Algebra.TensorProduct.map π ππ).comp
                  (Algebra.TensorProduct.map (AlgHom.id K B₀) Δ₀) := by
        rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
          hΔAπ', AlgHom.comp_id, AlgHom.id_comp]

      have keyAssoc : ∀ z : (B₀ ⊗[K] B₀) ⊗[K] B₀,
          (↑(Algebra.TensorProduct.assoc K K K A A A) : _ →ₐ[K] _)
            ((Algebra.TensorProduct.map ππ π) z)
          = (Algebra.TensorProduct.map π ππ)
              ((↑(Algebra.TensorProduct.assoc K K K B₀ B₀ B₀) : _ →ₐ[K] _) z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul xy w =>
          induction xy using TensorProduct.induction_on with
          | zero => simp
          | tmul x y =>
            simp only [Algebra.TensorProduct.map_tmul, hππ_tmul]
            rfl
          | add p q hp hq =>
            simp only [TensorProduct.add_tmul, map_add, hp, hq]
        | add p q hp hq => simp only [map_add, hp, hq]

      have hB₀coassoc : ∀ b : B₀,
          (↑(Algebra.TensorProduct.assoc K K K B₀ B₀ B₀) : _ →ₐ[K] _)
            ((Algebra.TensorProduct.map Δ₀ (AlgHom.id K B₀)) (Δ₀ b))
          = (Algebra.TensorProduct.map (AlgHom.id K B₀) Δ₀) (Δ₀ b) := by
        intro b
        have h := DFunLike.congr_fun (Coalgebra.coassoc (R := K) (A := B₀)) b

        exact h
      refine AlgHom.ext (fun a => ?_)
      obtain ⟨b, rfl⟩ := hπsurj a
      simp only [AlgHom.comp_apply, hΔAπ]
      have step1 : (Algebra.TensorProduct.map ΔA (AlgHom.id K A)) (ππ (Δ₀ b))
                 = (Algebra.TensorProduct.map ππ π)
                     ((Algebra.TensorProduct.map Δ₀ (AlgHom.id K B₀)) (Δ₀ b)) :=
        DFunLike.congr_fun keyL (Δ₀ b)
      have step4 : (Algebra.TensorProduct.map (AlgHom.id K A) ΔA) (ππ (Δ₀ b))
                 = (Algebra.TensorProduct.map π ππ)
                     ((Algebra.TensorProduct.map (AlgHom.id K B₀) Δ₀) (Δ₀ b)) :=
        DFunLike.congr_fun keyR (Δ₀ b)
      rw [step1, keyAssoc, hB₀coassoc b, ← step4])
    (by

      apply algHom_surj_ext
      intro b
      simp only [AlgHom.comp_apply, hΔAπ]

      have step1 : (Algebra.TensorProduct.map εA (AlgHom.id K A)).comp ππ
                 = Algebra.TensorProduct.map ε₀ π := by
        rw [← Algebra.TensorProduct.map_comp, hεAπ', AlgHom.id_comp]
      have step2 : ∀ x : B₀ ⊗[K] B₀,
          (Algebra.TensorProduct.map ε₀ π) x
          = (Algebra.TensorProduct.map (AlgHom.id K K) π)
              ((ε₀.toLinearMap.rTensor B₀) x) := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
        | add p q hp hq => simp [map_add, hp, hq]
      rw [show (Algebra.TensorProduct.map εA (AlgHom.id K A)) (ππ (Δ₀ b))
            = (Algebra.TensorProduct.map ε₀ π) (Δ₀ b) from
          DFunLike.congr_fun step1 (Δ₀ b)]
      rw [step2]
      change (Algebra.TensorProduct.map (AlgHom.id K K) π)
        (((Coalgebra.counit (R := K)).rTensor B₀) (Coalgebra.comul (R := K) b)) = _
      rw [Coalgebra.rTensor_counit_comul (R := K) b]
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_symm_apply])
    (by

      apply algHom_surj_ext
      intro b
      simp only [AlgHom.comp_apply, hΔAπ]
      have step1 : (Algebra.TensorProduct.map (AlgHom.id K A) εA).comp ππ
                 = Algebra.TensorProduct.map π ε₀ := by
        rw [← Algebra.TensorProduct.map_comp, hεAπ', AlgHom.id_comp]
      have step2 : ∀ x : B₀ ⊗[K] B₀,
          (Algebra.TensorProduct.map π ε₀) x
          = (Algebra.TensorProduct.map π (AlgHom.id K K))
              ((ε₀.toLinearMap.lTensor B₀) x) := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
        | add p q hp hq => simp [map_add, hp, hq]
      rw [show (Algebra.TensorProduct.map (AlgHom.id K A) εA) (ππ (Δ₀ b))
            = (Algebra.TensorProduct.map π ε₀) (Δ₀ b) from
          DFunLike.congr_fun step1 (Δ₀ b)]
      rw [step2]
      change (Algebra.TensorProduct.map π (AlgHom.id K K))
        (((Coalgebra.counit (R := K)).lTensor B₀) (Coalgebra.comul (R := K) b)) = _
      rw [Coalgebra.lTensor_counit_comul (R := K) b]
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_symm_apply])
  have hcomulA_eq : ∀ a : A, Coalgebra.comul (R := K) a = ΔA a := fun a => rfl
  have hcounitA_eq : ∀ a : A, Coalgebra.counit (R := K) a = εA a := fun a => rfl

  have hSAHI : ∀ x ∈ I, (π.comp S₀AH) x = 0 := vanish_on_I (π.comp S₀AH)
    (by
      show π (S₀ (P - 1)) = 0
      rw [map_sub, hSP, hS1, map_sub, hπP, map_one, sub_self])
    (by
      show π (S₀ Q) = 0
      rw [hSQ, map_neg, hπQ, neg_zero])
  let SA : A →ₐ[K] A := Ideal.Quotient.liftₐ I (π.comp S₀AH) hSAHI
  have hSAπ : ∀ b, SA (π b) = π (S₀ b) := fun b => rfl

  have hmul'_ππ : ∀ x : B₀ ⊗[K] B₀, LinearMap.mul' K A (ππ x) = π (LinearMap.mul' K B₀ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hππ_tmul, LinearMap.mul'_apply, map_mul]
    | add p q hp hq => simp [map_add, hp, hq]
  have hrT_ππ : ∀ x : B₀ ⊗[K] B₀,
      (SA.toLinearMap.rTensor A) (ππ x) = ππ ((S₀.rTensor B₀) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hππ_tmul, LinearMap.rTensor_tmul, hSAπ]
    | add p q hp hq => simp [map_add, hp, hq]
  have hlT_ππ : ∀ x : B₀ ⊗[K] B₀,
      (SA.toLinearMap.lTensor A) (ππ x) = ππ ((S₀.lTensor B₀) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hππ_tmul, LinearMap.lTensor_tmul, hSAπ]
    | add p q hp hq => simp [map_add, hp, hq]

  letI instHopfA : HopfAlgebra K A :=
    { antipode := SA.toLinearMap
      mul_antipode_rTensor_comul := by
        ext a
        obtain ⟨b, rfl⟩ := hπsurj a
        simp only [LinearMap.comp_apply, hcomulA_eq, hΔAπ, hrT_ππ, hmul'_ππ,
          hcounitA_eq, hεAπ, Algebra.linearMap_apply]
        rw [hSax b, AlgHom.commutes]
      mul_antipode_lTensor_comul := by
        ext a
        obtain ⟨b, rfl⟩ := hπsurj a
        simp only [LinearMap.comp_apply, hcomulA_eq, hΔAπ, hlT_ππ, hmul'_ππ,
          hcounitA_eq, hεAπ, Algebra.linearMap_apply]
        rw [hSaxL b, AlgHom.commutes] }

  have hcomm_ππ : ∀ x : B₀ ⊗[K] B₀,
      (TensorProduct.comm K A A) (ππ x) = ππ ((TensorProduct.comm K B₀ B₀) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hππ_tmul, TensorProduct.comm_tmul]
    | add p q hp hq => simp [map_add, hp, hq]
  have instCocommA : Coalgebra.IsCocomm K A := by
    constructor
    ext a
    obtain ⟨b, rfl⟩ := hπsurj a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcomulA_eq, hΔAπ, hcomm_ππ]
    congr 1
    exact DFunLike.congr_fun hcc₀.comm_comp_comul b

  have hgen' : Algebra.adjoin K {π u₀, π v₀} = (⊤ : Subalgebra K A) := by
    rw [eq_top_iff]
    rintro a -
    obtain ⟨b, rfl⟩ := hπsurj a
    have hb : b ∈ Algebra.adjoin K {u₀, v₀} := hgen₀ ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (Set.mem_insert _ _)
      · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  have hrel' : (π u₀) ^ 2 - algebraMap K A c * (π v₀) ^ 2 = 1 := by
    have := congrArg π hrel₀
    simp only [map_sub, map_pow, map_mul, map_one, AlgHom.commutes] at this
    exact this
  have hcu' : Coalgebra.comul (R := K) (π u₀)
      = (π u₀) ⊗ₜ[K] (π u₀) + c • ((π v₀) ⊗ₜ[K] (π v₀)) := by
    rw [hcomulA_eq, hΔAπ, show Δ₀ u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀) from hcu₀]
    simp only [map_add, map_smul, hππ_tmul]
  have hcv' : Coalgebra.comul (R := K) (π v₀)
      = (π u₀) ⊗ₜ[K] (π v₀) + (π v₀) ⊗ₜ[K] (π u₀) := by
    rw [hcomulA_eq, hΔAπ, show Δ₀ v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀ from hcv₀]
    simp only [map_add, hππ_tmul]
  have hfact : ∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 →
      ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g := fun g hgP hgQ =>
    ⟨Ideal.Quotient.liftₐ I g
      (vanish_on_I g (by rw [map_sub, map_one, hgP]; ring) hgQ),
      AlgHom.ext fun b => rfl⟩

  exact ⟨A, inferInstance, instHopfA, instCocommA, π u₀, π v₀, π,
    rfl, rfl, hπP, hπQ, hfact, hgen', hrel', hcu', hcv'⟩

end S_HopfAlgebra_exists_normOneTorus_hopfIdeal_quotient_of_powerPair
end P2MW
export P2MW.S_HopfAlgebra_exists_normOneTorus_hopfIdeal_quotient_of_powerPair (solution)
