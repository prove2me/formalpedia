-- Prove2me | solution 1 for ModularCurve.heckeNilpotent_of_model_jZero_torsion_heckeNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bd60f68a-e32d-5d90-8632-f9962044847e

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeNilpotent_of_model_jZero_torsion_heckeNilpotent

open ModularCurve WithConv

namespace KTailK1

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
  [Module.Free R B] [Module.Finite R B] {K : Type*} [Field K] [Algebra R K]

private theorem apply_eq_sum (v : Module.Basis (Module.Free.ChooseBasisIndex R B) R B)
    (x : B →ₐ[R] K) (y : B) :
    x y = ∑ j, algebraMap R K (v.repr y j) * x (v j) := by
  conv_lhs => rw [← v.sum_repr y]
  simp [map_sum, Algebra.smul_def]

private theorem eq_zero_of_forall_algHom_eq_zero (hinj : Function.Injective (algebraMap R K))
    (hcard : Nat.card (B →ₐ[R] K) = Module.finrank R B) (b : B) (hb : ∀ x : B →ₐ[R] K, x b = 0) :
    b = 0 := by
  classical
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  let v := Module.Free.chooseBasis R B
  by_cases hι : IsEmpty (Module.Free.ChooseBasisIndex R B)
  · apply v.repr.injective
    ext i
    exact hι.elim i
  rw [not_isEmpty_iff] at hι
  have hn : Module.finrank R B ≠ 0 := by
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact Fintype.card_ne_zero
  haveI : Finite (B →ₐ[R] K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn)
  letI := Fintype.ofFinite (B →ₐ[R] K)
  have hc : Fintype.card (Module.Free.ChooseBasisIndex R B) = Fintype.card (B →ₐ[R] K) := by
    rw [← Nat.card_eq_fintype_card (α := B →ₐ[R] K), hcard, Module.finrank_eq_card_chooseBasisIndex]
  let σ := Fintype.equivOfCardEq hc
  let M : Matrix (Module.Free.ChooseBasisIndex R B) (Module.Free.ChooseBasisIndex R B) K :=
    fun i j => σ i (v j)

  have hDed : LinearIndependent K (fun i => ((σ i : B →ₐ[R] K) : B → K)) := by
    have h2 : Function.Injective (fun i => ((σ i : B →ₐ[R] K) : B →* K)) :=
      AlgHom.coe_monoidHom_injective.comp σ.injective
    have h3 := (linearIndependent_monoidHom B K).comp _ h2
    exact h3
  have hrows : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff] at hDed ⊢
    intro c hc0 i
    have hcol : ∀ j, ∑ i, c i * M i j = 0 := by
      intro j
      have := congr_fun hc0 j
      simpa [Finset.sum_apply, Matrix.row] using this
    refine hDed c ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc ∑ i, c i * σ i y
        = ∑ i, c i * ∑ j, algebraMap R K (v.repr y j) * M i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [apply_eq_sum v (σ i) y]
      _ = ∑ j, algebraMap R K (v.repr y j) * ∑ i, c i * M i j := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by simp [hcol]
  have hmv : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)

  have hvec : M.mulVec (fun j => algebraMap R K (v.repr b j)) = M.mulVec 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    have hbi := hb (σ i)
    rw [apply_eq_sum v] at hbi
    simpa [Matrix.mulVec, dotProduct, M, mul_comm] using hbi
  have hr := congr_fun (hmv hvec)
  apply v.repr.injective
  ext j
  have hj : algebraMap R K (v.repr b j) = algebraMap R K 0 := by
    rw [map_zero]
    exact hr j
  simpa using hinj hj

private theorem eq_of_forall_algHom_eq (hinj : Function.Injective (algebraMap R K))
    (hcard : Nat.card (B →ₐ[R] K) = Module.finrank R B) {b₁ b₂ : B}
    (h : ∀ x : B →ₐ[R] K, x b₁ = x b₂) : b₁ = b₂ := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_algHom_eq_zero hinj hcard (b₁ - b₂) fun x => by rw [map_sub, h x, sub_self]

end KTailK1

namespace KTailK1

section Base
variable (p : ℕ)

private theorem algebraMap_injective :
    Function.Injective (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
  rw [IsScalarTower.algebraMap_eq (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective

end Base

set_option maxHeartbeats 4000000 in

private theorem tp_nilpotent
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (φ' : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar M
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ' t h)) → ((e g : JZero M)) = t • (e f : JZero M))
    (Tc : H →ₐc[GaloisRep.ratLocalizedAt p] H)
    (hTc : (Tc : H →ₐ[GaloisRep.ratLocalizedAt p] H) = φ' (heckeGen ⟨p, hp.out⟩)) :
    ∃ m : ℕ, (Tc : H →ₗ[GaloisRep.ratLocalizedAt p] H) ^ m =
      Algebra.linearMap (GaloisRep.ratLocalizedAt p) H ∘ₗ Coalgebra.counit := by
  classical
  letI instJ : Module HeckeAlg (JZero M) := heckeModuleBar M

  by_cases hι : IsEmpty (Module.Free.ChooseBasisIndex (GaloisRep.ratLocalizedAt p) H)
  · haveI : Subsingleton H :=
      (Module.Free.chooseBasis (GaloisRep.ratLocalizedAt p) H).repr.toEquiv.subsingleton
    exact ⟨0, Subsingleton.elim _ _⟩
  rw [not_isEmpty_iff] at hι
  haveI : Nontrivial (GaloisRep.ratLocalizedAt p) := inferInstance
  have hcard := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero (GaloisRep.ratLocalizedAt p) H
    (AlgebraicClosure ℚ)
  have hn : Module.finrank (GaloisRep.ratLocalizedAt p) H ≠ 0 := by
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact Fintype.card_ne_zero
  haveI : Finite (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn)
  haveI : Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
    Finite.of_equiv _ (WithConv.equiv _).symm
  letI := Fintype.ofFinite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
  have sepH : ∀ {a b : H},
      (∀ x : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, x a = x b) → a = b :=
    fun h => eq_of_forall_algHom_eq (algebraMap_injective p) hcard h

  have hE : ∀ {x y : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)},
      ((e x : JZero M)) = (e y : JZero M) → x = y :=
    fun h => e.injective (Subtype.ext h)
  have hadd : ∀ x y : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ((e (x * y) : JZero M)) = (e x : JZero M) + (e y : JZero M) := by
    intro x y
    rw [he_add]
    rfl
  have hone : ((e 1 : JZero M)) = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : (e 1 : JZero M) + (e 1 : JZero M) = (e 1 : JZero M) + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h'

  let T : Nat.Primes := ⟨p, hp.out⟩
  let pull : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    fun x => toConv (x.ofConv.comp (φ' (heckeGen T)))
  have hpull : ∀ x, ((e (pull x) : JZero M)) = heckeGen T • (e x : JZero M) :=
    fun x => hφ (heckeGen T) x (pull x) (fun h => rfl)
  have hpull_iter : ∀ (k : ℕ) (x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      ((e (pull^[k] x) : JZero M)) = (heckeOperatorBar M T ^ k) (e x : JZero M) ∨
        ¬ HeckeOperatorsCommuteBar M := by
    intro k x
    by_cases hc : HeckeOperatorsCommuteBar M
    · left
      induction k generalizing x with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply, ih (pull x), hpull, heckeModuleBar_heckeGen_smul hc,
          pow_succ, Module.End.mul_apply]
    · right
      exact hc
  have hpull_one : pull 1 = 1 := hE (by rw [hpull, hone, smul_zero])

  have hkill : ∀ x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ∃ k : ℕ, pull^[k] x = 1 := by
    intro x
    by_cases hc : HeckeOperatorsCommuteBar M
    · have hmem : (e x : JZero M) ∈ ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M T ^ m) :=
        (Submodule.mem_inf.mp (e x).2).2
      have hdir : Directed (· ≤ ·) fun m : ℕ => LinearMap.ker (heckeOperatorBar M T ^ m) := by
        refine Monotone.directed_le fun a b hab y hy => ?_
        rw [LinearMap.mem_ker] at hy ⊢
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
        rw [add_comm, pow_add, Module.End.mul_apply, hy, map_zero]
      obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hmem
      refine ⟨k, hE ?_⟩
      rcases hpull_iter k x with h | h
      · rw [h, hone]
        exact LinearMap.mem_ker.mp hk
      · exact absurd hc h
    · refine ⟨1, hE ?_⟩
      rw [Function.iterate_one, hpull, heckeModuleBar_heckeGen_smul_of_not hc, hone]
  choose kf hkf using hkill
  let m : ℕ := Finset.univ.sup kf
  have hm : ∀ x, pull^[m] x = 1 := by
    intro x
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := kf) (Finset.mem_univ x))
    have hm' : m = c + kf x := by
      show Finset.univ.sup kf = c + kf x
      rw [hc, add_comm]
    rw [hm', Function.iterate_add_apply, hkf]
    clear hc hm'
    induction c with
    | zero => rfl
    | succ c ih => rw [Function.iterate_succ_apply', ih, hpull_one]

  have hiter : ∀ (k : ℕ) (x : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) (h : H),
      (pull^[k] (toConv x)).ofConv h = x ((⇑(φ' (heckeGen T)))^[k] h) := by
    intro k x
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
      exact ih (φ' (heckeGen T) h)
  refine ⟨m, ?_⟩
  ext h
  rw [Module.End.pow_apply]
  have hTc' : ∀ y : H, (Tc : H →ₗ[GaloisRep.ratLocalizedAt p] H) y = φ' (heckeGen T) y := by
    intro y
    rw [← hTc]
    rfl
  have hfun : ⇑(Tc : H →ₗ[GaloisRep.ratLocalizedAt p] H) = ⇑(φ' (heckeGen T)) := funext hTc'
  rw [hfun]
  apply sepH
  intro x
  rw [← hiter m x h, hm (toConv x)]
  simp [AlgHom.convOne_apply, Algebra.linearMap_apply]

end KTailK1

set_option maxHeartbeats 4000000 in

theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (φ' : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar M
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ' t h)) → ((e g : JZero M)) = t • (e f : JZero M))
    (Tc : H →ₐc[GaloisRep.ratLocalizedAt p] H)
    (hTc : (Tc : H →ₐ[GaloisRep.ratLocalizedAt p] H) = φ' (heckeGen ⟨p, hp.out⟩)) :
    ∃ m : ℕ, (Tc : H →ₗ[GaloisRep.ratLocalizedAt p] H) ^ m =
      Algebra.linearMap (GaloisRep.ratLocalizedAt p) H ∘ₗ Coalgebra.counit :=
  KTailK1.tp_nilpotent M p H e he_add φ' hφ Tc hTc

end S_ModularCurve_heckeNilpotent_of_model_jZero_torsion_heckeNilpotent
end P2MW
export P2MW.S_ModularCurve_heckeNilpotent_of_model_jZero_torsion_heckeNilpotent (solution)
