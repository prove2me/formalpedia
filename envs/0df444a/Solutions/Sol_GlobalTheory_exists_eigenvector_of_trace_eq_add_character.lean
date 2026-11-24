-- Prove2me | solution 1 for GlobalTheory.exists_eigenvector_of_trace_eq_add_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:14.877681+00:00
-- url     : https://prove2.me/submissions/e5e2c85d-3746-4161-8300-dd2f6ec657b6

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEigenvectorOfTraceEqAddCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma exists_char_augmentation_zero_acting_as_one {K Γ V : Type} [Field K] [Group Γ]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V)
    (χ : Γ →* Kˣ) (hs : ρ.IsSemisimpleRepresentation)
    (hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0) :
    ∃ x : MonoidAlgebra K Γ, MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) x = 0 ∧
      ρ.asAlgebraHom x = 1 := by
  set ε := MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) with hε
  have hsm : IsSemisimpleModule (MonoidAlgebra K Γ) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs
  let b := Module.finBasis K V
  let m : Fin (Module.finrank K V) → ρ.asModule := fun i => ρ.asModuleEquiv.symm (b i)
  let P : Submodule (MonoidAlgebra K Γ) (Fin (Module.finrank K V) → ρ.asModule) :=
    Submodule.map (LinearMap.toSpanSingleton (MonoidAlgebra K Γ) _ m)
      (RingHom.ker (ε : MonoidAlgebra K Γ →+* K))
  obtain ⟨C, hC⟩ := exists_isCompl P
  have hm : m ∈ P ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp hm
  have hkill : ∀ x, ε x = 0 → x • c = 0 := by
    intro x hx
    have h1 : x • c ∈ P := by
      have : x • c = x • m - x • p := by rw [← hpc, smul_add, add_sub_cancel_left]
      rw [this]
      exact P.sub_mem (Submodule.mem_map.mpr ⟨x, RingHom.mem_ker.mpr hx,
        LinearMap.toSpanSingleton_apply _ _ _ _⟩) (P.smul_mem x hp)
    have h2 : x • c ∈ P ⊓ C := Submodule.mem_inf.mpr ⟨h1, C.smul_mem x hc⟩
    rwa [hC.inf_eq_bot, Submodule.mem_bot] at h2
  have hc0 : c = 0 := by
    funext i
    have hv := hno (ρ.asModuleEquiv (c i)) fun g => by
      have h := congrFun (hkill (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 ((χ g : Kˣ) : K))
        (by simp [hε, MonoidAlgebra.lift_single])) i
      change ρ.asModuleEquiv.symm (ρ.asAlgebraHom _ (ρ.asModuleEquiv (c i))) = 0 at h
      rw [LinearEquiv.map_eq_zero_iff, map_sub, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, one_smul, map_one, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h
    simpa using hv
  rw [hc0, add_zero] at hpc
  obtain ⟨y, hy, hym⟩ := Submodule.mem_map.mp (show m ∈ P from hpc ▸ hp)
  refine ⟨y, RingHom.mem_ker.mp hy, b.ext fun i => ?_⟩
  have h := congrFun hym i
  change ρ.asModuleEquiv.symm (ρ.asAlgebraHom y (ρ.asModuleEquiv (ρ.asModuleEquiv.symm (b i)))) =
    ρ.asModuleEquiv.symm (b i) at h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] at h
  simpa using h
private lemma false_of_trace_pow_eq_card_add_one_sub {L ι : Type} [Field L] [CharZero L] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (h : ∀ n : ℕ, (M ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n) :
    False := by
  set D : L := (Fintype.card ι : L) + 1 with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact Nat.cast_add_one_ne_zero _
  have hpoly : ∀ f : Polynomial L, (Polynomial.aeval M f).trace = D * f.eval 1 - f.eval 0 := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add, Matrix.trace_add, hf, hg, Polynomial.eval_add]; ring
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.trace_smul, h n, Polynomial.eval_monomial, Polynomial.eval_monomial, one_pow,
        smul_eq_mul]
      ring
  set p := M.charpoly with hp
  have hvan : ∀ g : Polynomial L, D * (g * p).eval 1 - (g * p).eval 0 = 0 := by
    intro g
    rw [← hpoly, map_mul, hp, Matrix.aeval_self_charpoly, mul_zero, Matrix.trace_zero]
  have hp1 : p.eval 1 = 0 := by
    have := hvan Polynomial.X
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hD0
  have hp0 : p.eval 0 = 0 := by
    have := hvan 1
    simpa [hp1] using this
  have hpne : p ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpne 1
  set b := p.rootMultiplicity 1
  have hb : 0 < b := (Polynomial.rootMultiplicity_pos hpne).mpr hp1
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C (1 : L)) ^ b) q :=
    ((Polynomial.irreducible_X_sub_C (1 : L)).coprime_iff_not_dvd.mpr hq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hq0 : q.eval 0 = 0 := by
    have := hp0
    rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (by norm_num))
  have he1 : (v * q).eval 1 = 1 := by
    have := congrArg (Polynomial.eval 1) huv
    simpa [Polynomial.eval_mul, zero_pow hb.ne'] using this
  have he0 : (v * q).eval 0 = 0 := by simp [Polynomial.eval_mul, hq0]
  have hidem : (v * q) * (v * q) = v * q - (u * v) * p := by
    rw [hpq]; linear_combination (v * q) * huv
  set E := Polynomial.aeval M (v * q) with hE
  have hEE : E * E = E := by
    rw [hE, ← map_mul, hidem, map_sub, map_mul (Polynomial.aeval M) (u * v) p, hp,
      Matrix.aeval_self_charpoly, mul_zero, sub_zero]
  have htrE : E.trace = D := by rw [hE, hpoly, he1, he0]; ring
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hEE]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [LinearMap.trace_eq_matrix_trace L (Pi.basisFun L ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', htrE, hD] at htr
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' E))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have : Fintype.card ι + 1 = Module.finrank L (LinearMap.range (Matrix.toLin' E)) := by
    exact_mod_cast htr
  omega
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K L Γ V ι : Type) [Field K] [Field L] [CharZero L] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (φ : K →+* L) (ρ : Representation K Γ V) (σ : Γ →* Matrix ι ι L) (χ : Γ →* Kˣ), ρ.IsSemisimpleRepresentation → (∀ g, φ (LinearMap.trace K V (ρ g)) = (σ g).trace + φ ((χ g : Kˣ) : K)) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
  intro K L Γ V ι _ _ _ _ _ _ _ _ _ φ ρ σ χ hs htr
  by_contra hcon
  push_neg at hcon
  have hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0 := fun v hv => by
    by_contra h0
    obtain ⟨g, hg⟩ := hcon v h0
    exact hg (hv g)
  obtain ⟨x, hx, hρx⟩ := exists_char_augmentation_zero_acting_as_one ρ χ hs hno
  let S : MonoidAlgebra K Γ →+* Matrix ι ι L :=
    MonoidAlgebra.liftNCRingHom ((Matrix.scalar ι).comp φ) σ
      (fun _ _ => Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hkey : ∀ z : MonoidAlgebra K Γ, φ (LinearMap.trace K V (ρ.asAlgebraHom z)) =
      (S z).trace + φ (MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) z) := by
    intro z
    refine MonoidAlgebra.induction_linear z ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add, Matrix.trace_add, hf, hg]; ring
    · intro g r
      rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, map_mul, htr g]
      have hS : S (MonoidAlgebra.single g r) = Matrix.scalar ι (φ r) * σ g := by
        simp [S, MonoidAlgebra.liftNCRingHom, MonoidAlgebra.liftNC_single]
      rw [hS]
      rw [MonoidAlgebra.lift_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        Matrix.trace_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
      ring
  have hdim := htr 1
  rw [map_one ρ, LinearMap.trace_one, map_natCast, map_one σ, Matrix.trace_one, map_one χ,
    Units.val_one, map_one φ] at hdim
  have hpow : ∀ n : ℕ, ((S x) ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n := by
    intro n
    have h1 := hkey (x ^ n)
    rw [map_pow, hρx, one_pow, LinearMap.trace_one, map_natCast, map_pow, map_pow, hx] at h1
    have h0 : φ ((0 : K) ^ n) = (0 : L) ^ n := by rw [map_pow, map_zero]
    linear_combination hdim - h1 - h0
  exact false_of_trace_pow_eq_card_add_one_sub (S x) hpow
end _root_.GlobalTheory
end GlobalTheory
