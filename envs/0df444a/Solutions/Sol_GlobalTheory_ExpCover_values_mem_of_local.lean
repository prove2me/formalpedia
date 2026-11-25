-- Prove2me | solution 1 for GlobalTheory.ExpCover.values_mem_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:41:43.98922+00:00
-- url     : https://prove2.me/submissions/f33155e9-0962-43ad-9c96-6fab57b6916a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuesMemOfLocal
import Theorems.Thm_GlobalTheory_maximal_ideal_eq_joint_eigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.ExpCover
set_option autoImplicit false in
private lemma coeffs_eq_zero_of_linearIndependent_of_injective {O K X : Type} [CommRing O] [IsDomain O] [Field K]
    (emb : O →+* K) (hemb : Function.Injective emb) :
    ∀ (n : ℕ) (α : Fin n → X → O), LinearIndependent O α →
      ∀ c : Fin n → K, (∀ x, ∑ j, c j * emb (α j x) = 0) → c = 0 := by
  intro n
  induction n with
  | zero => intro α _ c _; funext j; exact j.elim0
  | succ n ih =>
    intro α hα c hc
    have h0 : α 0 ≠ 0 := hα.ne_zero 0
    obtain ⟨x0, hx0⟩ : ∃ x0, α 0 x0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (funext h)
    have hea : emb (α 0 x0) ≠ 0 := fun h => hx0 (hemb (by rw [h, map_zero]))
    let β : Fin n → X → O := fun j x => α 0 x0 * α j.succ x - α j.succ x0 * α 0 x
    have hβ : LinearIndependent O β := by
      rw [Fintype.linearIndependent_iff] at hα ⊢
      intro d hd j
      have hd' : ∀ x, ∑ k, d k * β k x = 0 := fun x => by
        simpa [Finset.sum_apply] using congrFun hd x
      have key := hα (Fin.cons (-(∑ k, d k * α k.succ x0)) (fun k => d k * α 0 x0)) (by
        funext x
        have e1 : ∑ k, d k * β k x =
            α 0 x0 * ∑ k, d k * α k.succ x - (∑ k, d k * α k.succ x0) * α 0 x := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by simp only [β]; ring
        have e2 : ∑ k, d k * α 0 x0 * α k.succ x = α 0 x0 * ∑ k, d k * α k.succ x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        have h3 := hd' x
        rw [e1] at h3
        simp only [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero,
          Fin.cons_succ, Pi.zero_apply]
        rw [e2]
        linear_combination h3)
      have := key j.succ
      simp only [Fin.cons_succ] at this
      exact (mul_eq_zero.1 this).resolve_right hx0
    have hS : ∀ x, c 0 * emb (α 0 x) + ∑ j : Fin n, c j.succ * emb (α j.succ x) = 0 := fun x => by
      simpa [Fin.sum_univ_succ] using hc x
    have hrel : ∀ x, ∑ j, c j.succ * emb (β j x) = 0 := by
      intro x
      have e : ∑ j, c j.succ * emb (β j x) = emb (α 0 x0) * ∑ j : Fin n, c j.succ * emb (α j.succ x)
          - (∑ j : Fin n, c j.succ * emb (α j.succ x0)) * emb (α 0 x) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [β, map_sub, map_mul]; ring
      rw [e]
      linear_combination emb (α 0 x0) * hS x - emb (α 0 x) * hS x0
    have htail := ih β hβ (fun j => c j.succ) hrel
    have htail' : ∀ j : Fin n, c j.succ = 0 := fun j => congrFun htail j
    have hc0 : c 0 = 0 := by
      have := hS x0
      simp only [htail', zero_mul, Finset.sum_const_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hea
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hc0
    · exact htail' k
end GlobalTheory.ExpCover
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ExpCover
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.ExpCover
namespace _root_.GlobalTheory.ExpCover
theorem _root_.solution {l : ℕ} [Fact l.Prime] {O I G V W : Type} [CommRing O]
    [IsDomain O] [IsPrincipalIdealRing O] [Mul G]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [AddCommGroup W] [Module (PadicAlgCl l) W]
    (M : Submodule O (G → V)) [hm : Module (MvPolynomial I O) M] [@IsScalarTower O (MvPolynomial I O) M _ hm.toSMul _]
    [Module.Finite O M]
    (emb : O →+* PadicAlgCl l) (hemb : Function.Injective emb)
    (h1 : ∀ c, ‖emb c‖ ≤ 1) (hu : ∀ c, ‖emb c‖ = 1 → IsUnit c) (b : V →ₛₗ[emb] W) (hb : Function.Injective b)
    (hli : ∀ (n : ℕ) (y : Fin n → V), LinearIndependent O y → LinearIndependent (PadicAlgCl l) fun j => b (y j))
    (tr : I → Finset G) (cst : I → O)
    (hX : ∀ i (f : M) g, (((X i : MvPolynomial I O) • f : M) : G → V) g = cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule O V) (S : Submodule (PadicAlgCl l) (G → W))
    (hS : ∀ i, ∀ u ∈ S, _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i) u ∈ S)
    (x : M) (hx : (fun g => b ((x : G → V) g)) ∈ S) (a : O) (J : ℕ) (D : Set M) (hD : ∀ y ∈ D, ∀ g, (y : G → V) g ∈ U)
    (hloc : ∀ (m : Ideal (MvPolynomial I O)) (hmax : m.IsMaximal) (θ : I → PadicAlgCl l), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) →
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) →
      ∀ y : LocalizedModule (haveI := hmax.isPrime; m.primeCompl) M,
        ∃ x' ∈ D, ∃ s : (haveI := hmax.isPrime; m.primeCompl),
          LocalizedModule.mk x' s = (algebraMap O (MvPolynomial I O) a) ^ J • y) :
    ∀ g, ((a ^ J • x : M) : G → V) g ∈ U := by
  classical
  let N : Submodule (MvPolynomial I O) M :=
    { carrier := {y | ∀ g, (y : G → V) g ∈ U}
      add_mem' := fun {y z} hy hz g => by
        simpa using U.add_mem (hy g) (hz g)
      zero_mem' := fun g => by simp
      smul_mem' := fun p y hy => by
        induction p using MvPolynomial.induction_on with
        | C c =>
          intro g
          have h : (C c : MvPolynomial I O) • y = c • y := by
            rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
          rw [h, Submodule.coe_smul, Pi.smul_apply]
          exact U.smul_mem c (hy g)
        | add p q hp hq =>
          intro g
          rw [add_smul]
          simpa using U.add_mem (hp g) (hq g)
        | mul_X p i hp =>
          intro g
          rw [mul_comm, mul_smul, hX i (p • y) g]
          exact U.smul_mem _ (U.sum_mem fun s _ => hp (g * s)) }
  set z : M := a ^ J • x with hz_def
  let A : Ideal (MvPolynomial I O) := N.comap (LinearMap.toSpanSingleton (MvPolynomial I O) M z)
  have hA : ∀ p, p ∈ A ↔ p • z ∈ N := fun p => Iff.rfl
  show z ∈ N
  by_contra hzN
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hzN
    have h1' : (1 : MvPolynomial I O) ∈ A := h ▸ Submodule.mem_top
    simpa using (hA 1).1 h1'
  obtain ⟨m, hmax, hAm⟩ := Ideal.exists_le_maximal A hAtop
  have key : ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) ∧
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) := by
    haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.of_smul_eq_zero fun r w h => by
      have h' : emb r • b w = 0 := by rw [← map_smulₛₗ, h, map_zero]
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (hemb (by rw [h'', map_zero]))
      · exact Or.inr (hb (by rw [h'', map_zero]))
    let Z : Submodule (MvPolynomial I O) M := Submodule.span (MvPolynomial I O) {x}
    let ι : Z →ₗ[O] (G → V) := M.subtype ∘ₗ (Z.subtype.restrictScalars O)
    have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
    haveI : Module.IsTorsionFree O Z := hι.moduleIsTorsionFree _ (by simp)
    haveI : Module.Finite O Z :=
      Module.Finite.of_injective (Z.subtype.restrictScalars O) Subtype.val_injective
    haveI : Module.Free O Z := Module.free_of_finite_type_torsion_free'
    let B := Module.finBasis O Z
    let φ : MvPolynomial I O →ₐ[O] Module.End O Z := Algebra.lsmul O O Z
    let ρ : MvPolynomial I O →ₐ[O] Matrix (Fin (Module.finrank O Z)) (Fin (Module.finrank O Z)) O :=
      (LinearMap.toMatrixAlgEquiv B).toAlgHom.comp φ
    have hxZ : x ∈ Z := Submodule.subset_span rfl
    have hker : ∀ p ∈ RingHom.ker ρ, p • x = 0 := by
      intro p hp
      have h0 : φ p = 0 := by
        have : ρ p = 0 := hp
        exact (LinearMap.toMatrixAlgEquiv B).injective (by simpa [ρ] using this)
      have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x, hxZ⟩)
      simpa [φ] using this
    obtain ⟨θ, hθ1, hθm, c, hc0, hc⟩ := _root_.GlobalTheory.maximal_ideal_eq_joint_eigen l O emb h1 hu I
      (Module.finrank O Z) ρ m hmax (fun p hp => hAm ((hA p).2 (by
        rw [hz_def, smul_comm, hker p hp, smul_zero]; exact N.zero_mem)))
    have hpS : ∀ p : MvPolynomial I O, (fun g => b (((p • x : M) : G → V) g)) ∈ S := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        have e : (fun g => b ((((C r : MvPolynomial I O) • x : M) : G → V) g)) =
            emb r • fun g => b ((x : G → V) g) := by
          funext g
          rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
          simp [map_smulₛₗ]
        rw [e]; exact S.smul_mem _ hx
      | add p q hp hq =>
        have e : (fun g => b ((((p + q) • x : M) : G → V) g)) =
            (fun g => b (((p • x : M) : G → V) g)) + fun g => b (((q • x : M) : G → V) g) := by
          funext g; simp [add_smul]
        rw [e]; exact S.add_mem hp hq
      | mul_X p i hp =>
        have e : (fun g => b ((((p * X i) • x : M) : G → V) g)) =
            _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i)
              (fun g => b (((p • x : M) : G → V) g)) := by
          funext g
          rw [mul_comm, mul_smul, hX]
          simp [_root_.GlobalTheory.ExpCover.transOp, map_sum, map_smulₛₗ]
        rw [e]; exact hS i _ hp
    have hZS : ∀ z ∈ Z, (fun g => b ((z : G → V) g)) ∈ S := by
      intro z hz
      obtain ⟨p, rfl⟩ := Submodule.mem_span_singleton.1 hz
      exact hpS p
    let f : Fin (Module.finrank O Z) → G → W := fun j g => b ((((B j : Z) : M) : G → V) g)
    have hind : LinearIndependent (PadicAlgCl l) f := by
      haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
      let w := Module.finBasis O V
      have hw := hli _ w w.linearIndependent
      let L : Z →ₗ[O] (G × Fin (Module.finrank O V) → O) :=
        LinearMap.pi fun p => (Finsupp.lapply p.2 ∘ₗ w.repr.toLinearMap) ∘ₗ (LinearMap.proj p.1 ∘ₗ ι)
      have hL : Function.Injective L := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply hι
        funext g
        apply w.repr.injective
        ext k
        have := congrFun hz (g, k)
        simpa [L] using this
      have hα := B.linearIndependent.map' L (LinearMap.ker_eq_bot.2 hL)
      rw [Fintype.linearIndependent_iff]
      intro c' hc'
      have hfk : ∀ j g, f j g = ∑ k, emb ((L ∘ B) j (g, k)) • b (w k) := by
        intro j g
        have e := congrArg b (w.sum_repr ((((B j : Z) : M) : G → V) g))
        rw [map_sum] at e
        simp only [map_smulₛₗ] at e
        show b ((((B j : Z) : M) : G → V) g) = _
        rw [← e]
        rfl
      have hzero : c' = 0 := coeffs_eq_zero_of_linearIndependent_of_injective emb hemb _ _ hα c' fun p => by
        have hg : ∑ j, c' j • f j p.1 = 0 := by simpa [Finset.sum_apply] using congrFun hc' p.1
        have hsum : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = 0 := by
          have e : ∑ k, (∑ j, c' j * emb ((L ∘ B) j (p.1, k))) • b (w k) = ∑ j, c' j • f j p.1 := by
            simp only [hfk, Finset.smul_sum, Finset.sum_smul, smul_smul]
            exact Finset.sum_comm
          rw [e, hg]
        exact (Fintype.linearIndependent_iff.1 hw) _ hsum p.2
      exact fun j => congrFun hzero j
    let v : G → W := ∑ j, c j • f j
    have hv_apply : ∀ h, v h = ∑ j, c j • f j h := by intro h; simp [v, Finset.sum_apply]
    refine ⟨θ, hθ1, hθm, v, S.sum_mem fun j _ => S.smul_mem _ (hZS _ (B j).2), ?_, ?_⟩
    · intro hv0
      exact hc0 (funext (Fintype.linearIndependent_iff.1 hind c hv0))
    · intro i g
      have hXB : ∀ j, emb (cst i) • ∑ s ∈ tr i, f j (g * s) = ∑ k, emb (ρ (X i) k j) • f k g := by
        intro j
        have e1 : (X i : MvPolynomial I O) • B j = ∑ k, ρ (X i) k j • B k := by
          conv_lhs => rw [← B.sum_repr ((X i : MvPolynomial I O) • B j)]
          simp [ρ, φ, LinearMap.toMatrixAlgEquiv_apply]
        calc emb (cst i) • ∑ s ∈ tr i, f j (g * s)
            = b ((((X i : MvPolynomial I O) • ((B j : Z) : M) : M) : G → V) g) := by
              rw [hX]; simp [f, map_sum, map_smulₛₗ]
          _ = b (((((X i : MvPolynomial I O) • B j : Z) : M) : G → V) g) := rfl
          _ = b ((((∑ k, ρ (X i) k j • B k : Z) : M) : G → V) g) := by rw [e1]
          _ = ∑ k, emb (ρ (X i) k j) • f k g := by
              simp [f, map_sum, map_smulₛₗ, Submodule.coe_sum, Finset.sum_apply]
      calc emb (cst i) • ∑ s ∈ tr i, v (g * s)
          = ∑ j, c j • (emb (cst i) • ∑ s ∈ tr i, f j (g * s)) := by
            simp only [hv_apply, Finset.smul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => smul_comm _ _ _
        _ = ∑ j, c j • ∑ k, emb (ρ (X i) k j) • f k g :=
            Finset.sum_congr rfl fun j _ => by rw [hXB]
        _ = ∑ k, (∑ j, emb (ρ (X i) k j) * c j) • f k g := by
            simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
        _ = ∑ k, (θ i * c k) • f k g := by
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 1
            have := congrFun (hc i) k
            simpa [Matrix.mulVec, dotProduct] using this
        _ = θ i • v g := by
            rw [hv_apply, Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
  obtain ⟨θ, hθ1, hθm, hv⟩ := key
  obtain ⟨x', hx'D, s, hs⟩ := hloc m hmax θ hθ1 hθm hv (LocalizedModule.mk x 1)
  rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hs
  obtain ⟨u, hu⟩ := hs
  have hpow : (algebraMap O (MvPolynomial I O) a) ^ J • x = z := by
    rw [← map_pow, algebraMap_smul]
  rw [hpow, one_smul] at hu
  have hmem : ((u : MvPolynomial I O) * (s : MvPolynomial I O)) • z ∈ N := by
    rw [mul_smul]
    change (u : MvPolynomial I O) • (s : MvPolynomial I O) • z ∈ N
    rw [← Submonoid.smul_def, ← Submonoid.smul_def, ← hu, Submonoid.smul_def]
    exact N.smul_mem _ (hD x' hx'D)
  have hus := hAm ((hA _).2 hmem)
  haveI := hmax.isPrime
  rcases hmax.isPrime.mem_or_mem hus with h | h
  · exact u.2 h
  · exact s.2 h
end _root_.GlobalTheory.ExpCover
end GlobalTheory.ExpCover
