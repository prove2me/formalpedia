-- Prove2me | solution 1 for GlobalTheory.AdLat.scale_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:23.427479+00:00
-- url     : https://prove2.me/submissions/1a952517-f449-4880-b4e8-ef7588c281cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZeroMemLatOf
import Theorems.Thm_GlobalTheory_AdLat_Scale_smul_mem_hat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat.Scale
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
end GlobalTheory.AdLat.Scale
namespace GlobalTheory.AdLat
open Scale
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem fv_smul' (c : E) (v : Fin n → E) :
    _root_.GlobalTheory.AdLat.fv F (c • v) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : _root_.GlobalTheory.AdLat.RA F E) •
        _root_.GlobalTheory.AdLat.fv F v := by
  funext i
  change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c * v i) =
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] v i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem smul_mem_latOf_of_smul_mem {L L' : Set (Fin n → E)} {c : E}
    (h : ∀ x ∈ L, c • x ∈ L') (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E))
    {v : Fin n → E} (hv : v ∈ _root_.GlobalTheory.AdLat.latOf F g L) :
    c • v ∈ _root_.GlobalTheory.AdLat.latOf F g L' := by
  obtain ⟨z, hz, hzv⟩ := hv
  refine ⟨_, _root_.GlobalTheory.AdLat.Scale.smul_mem_hat h hz, ?_⟩
  rw [Matrix.mulVec_smul, hzv, fv_smul']
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem fv_zero' :
    _root_.GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by
  funext i
  change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (0 : E) = 0
  rw [TensorProduct.tmul_zero]
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem zero_mem_latOf' {L : Set (Fin n → E)}
    (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) :
    (0 : Fin n → E) ∈ _root_.GlobalTheory.AdLat.latOf F g L :=
  ⟨0, zero_mem _, by rw [Matrix.mulVec_zero, fv_zero']⟩
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem fv_add' (v w : Fin n → E) :
    _root_.GlobalTheory.AdLat.fv F (v + w) =
      _root_.GlobalTheory.AdLat.fv F v + _root_.GlobalTheory.AdLat.fv F w := by
  funext i
  change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (v i + w i) = _ ⊗ₜ[F] v i + _ ⊗ₜ[F] w i
  rw [TensorProduct.tmul_add]
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem add_mem_latOf' {L : Set (Fin n → E)}
    (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) {v w : Fin n → E}
    (hv : v ∈ _root_.GlobalTheory.AdLat.latOf F g L)
    (hw : w ∈ _root_.GlobalTheory.AdLat.latOf F g L) :
    v + w ∈ _root_.GlobalTheory.AdLat.latOf F g L := by
  obtain ⟨z, hz, hzv⟩ := hv
  obtain ⟨y, hy, hyw⟩ := hw
  exact ⟨z + y, add_mem hz hy, by rw [Matrix.mulVec_add, hzv, hyw, fv_add']⟩
end GlobalTheory.AdLat
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
open Scale
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat
namespace _root_.GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (I : FractionalIdeal (𝓞 E)⁰ E) (L' : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → I ≠ 0 → L' = Submodule.span (𝓞 E) {w | ∃ a ∈ I, ∃ x ∈ L, w = a • x} → ((Submodule.span (𝓞 E) {w | ∃ a ∈ I, ∃ v ∈ _root_.GlobalTheory.AdLat.latOf F (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) L, w = a • v} : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = _root_.GlobalTheory.AdLat.latOf F (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) L' ∧ (AddSubgroup.closure {w | ∃ a ∈ I, ∃ z ∈ (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)).mulVec '' (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * z i} : Set (Fin n → _root_.GlobalTheory.AdLat.RA F E)) = (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)).mulVec '' (_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E))) ∧ L'.FG ∧ Submodule.span E (L' : Set (Fin n → E)) = ⊤ := by
  intro F E _ _ _ _ _ n L g I L' hLfg hLspan hI hL'
  set G : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E) :=
    (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) with hG
  have hgen : ∀ a ∈ I, ∀ x ∈ L, a • x ∈ L' := fun a ha x hx => by
    rw [hL']
    exact Submodule.subset_span ⟨a, ha, x, hx, rfl⟩
  have hinv : ∀ b ∈ I⁻¹, ∀ x ∈ (L' : Set (Fin n → E)), b • x ∈ (L : Set (Fin n → E)) := by
    intro b hb x hx
    rw [SetLike.mem_coe, hL'] at hx
    rw [SetLike.mem_coe]
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hw
      obtain ⟨r, hr⟩ :=
        (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hb a ha)
      rw [smul_smul, ← hr, algebraMap_smul]
      exact L.smul_mem r hy
    | zero => rw [smul_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
    | smul r w _ hw =>
      rw [← algebraMap_smul E r w, smul_comm, algebraMap_smul]
      exact L.smul_mem r hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      rw [SetLike.mem_coe] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨a, ha, v, hv, rfl⟩ := hw
        exact smul_mem_latOf_of_smul_mem (fun x hx => hgen a ha x hx) G hv
      | zero => exact zero_mem_latOf' G
      | add x y _ _ hx hy => exact add_mem_latOf' G hx hy
      | smul r w _ hw =>
        rw [← algebraMap_smul E r w]
        refine smul_mem_latOf_of_smul_mem (fun x hx => ?_) G hw
        rw [algebraMap_smul]
        exact L'.smul_mem r hx
    · intro v hv
      let N : Submodule (𝓞 E) (Fin n → E) := Submodule.span (𝓞 E)
        {w | ∃ a ∈ I, ∃ v ∈ _root_.GlobalTheory.AdLat.latOf F G L, w = a • v}
      let S : Submodule (𝓞 E) E :=
        { carrier := {c | c • v ∈ N}
          add_mem' := fun {c d} hc hd => by
            change (c + d) • v ∈ N
            rw [add_smul]
            exact N.add_mem hc hd
          zero_mem' := by
            change (0 : E) • v ∈ N
            rw [zero_smul]
            exact N.zero_mem
          smul_mem' := fun r c hc => by
            change (r • c) • v ∈ N
            rw [smul_assoc]
            exact N.smul_mem r hc }
      have hle : (I : Submodule (𝓞 E) E) * ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
          ≤ S := Submodule.mul_le.2 fun a ha b hb => by
        change (a * b) • v ∈ N
        rw [mul_smul]
        exact Submodule.subset_span ⟨a, ha, b • v, smul_mem_latOf_of_smul_mem (hinv b hb) G hv, rfl⟩
      have h1 : (1 : E) ∈ (I : Submodule (𝓞 E) E) *
          ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI]
        exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
      have h2 : (1 : E) • v ∈ N := hle h1
      rwa [one_smul] at h2
  · let φ : (Fin n → _root_.GlobalTheory.AdLat.RA F E) →+ (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
      AddMonoidHom.mk' (fun z => G *ᵥ z) (Matrix.mulVec_add G)
    have himage : G.mulVec '' (_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E)) :
        Set (Fin n → _root_.GlobalTheory.AdLat.RA F E)) =
        ((_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E))).map φ : Set _) :=
      (AddSubgroup.coe_map φ _).symm
    rw [himage]
    congr 1
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro w ⟨a, ha, z, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) • y,
        _root_.GlobalTheory.AdLat.Scale.smul_mem_hat (fun x hx => hgen a ha x hx) hy, ?_⟩
      change G *ᵥ (_ • y) = _
      rw [Matrix.mulVec_smul]
      rfl
    · rw [AddSubgroup.map_le_iff_le_comap]
      intro z hz
      unfold _root_.GlobalTheory.AdLat.hat at hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨b, hb, w, hw, rfl⟩ := hz
        rw [SetLike.mem_coe, hL'] at hw
        rw [show w = (1 : 𝓞 E) • w from (one_smul _ _).symm]
        generalize (1 : 𝓞 E) = r
        induction hw using Submodule.span_induction generalizing r with
        | mem w hw =>
          obtain ⟨a, ha, x, hx, rfl⟩ := hw
          have hy : r • x ∈ L := L.smul_mem r hx
          have heq : (fun i => b ⊗ₜ[F] (r • a • x) i) =
              ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) •
                fun i => b ⊗ₜ[F] (r • x) i := by
            funext i
            change b ⊗ₜ[F] (r • a • x) i =
              ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * (b ⊗ₜ[F] (r • x) i)
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
            congr 1
            simp only [Pi.smul_apply, smul_eq_mul, mul_smul_comm]
          change G *ᵥ (fun i => b ⊗ₜ[F] (r • a • x) i) ∈ AddSubgroup.closure _
          rw [heq, Matrix.mulVec_smul]
          exact AddSubgroup.subset_closure
            ⟨a, ha, _, ⟨_, AddSubgroup.subset_closure ⟨b, hb, r • x, hy, rfl⟩, rfl⟩, rfl⟩
        | zero =>
          have h0 : (fun i => b ⊗ₜ[F] (r • (0 : Fin n → E)) i) = 0 := by
            funext i
            simp
          rw [h0]
          exact zero_mem _
        | add x y _ _ hx hy =>
          have hxy : (fun i => b ⊗ₜ[F] (r • (x + y)) i) =
              (fun i => b ⊗ₜ[F] (r • x) i) + fun i => b ⊗ₜ[F] (r • y) i := by
            funext i
            simp [smul_add, TensorProduct.tmul_add]
          rw [hxy]
          exact add_mem (hx r) (hy r)
        | smul s w _ hw =>
          rw [smul_smul]
          exact hw (r * s)
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
  · obtain ⟨d, hd, hdI⟩ := I.isFractional
    have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero hd)
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
      (((algebraMap (𝓞 E) E d)⁻¹ • LinearMap.id : (Fin n → E) →ₗ[E] (Fin n → E))).restrictScalars
        (𝓞 E)
    have hle : L' ≤ L.map f := by
      rw [hL', Submodule.span_le]
      rintro w ⟨a, ha, x, hx, rfl⟩
      obtain ⟨r, hr⟩ := hdI a ha
      refine ⟨r • x, L.smul_mem r hx, ?_⟩
      change (algebraMap (𝓞 E) E d)⁻¹ • (r • x) = a • x
      rw [← algebraMap_smul E r x, hr, smul_smul, Algebra.smul_def d a, inv_mul_cancel_left₀ hd0]
    exact (hLfg.map f).of_le hle
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.2 hI)
    rw [eq_top_iff, ← hLspan, Submodule.span_le]
    intro x hx
    have hax : a • x ∈ Submodule.span E (L' : Set (Fin n → E)) :=
      Submodule.subset_span (hgen a ha x hx)
    have := Submodule.smul_mem _ a⁻¹ hax
    rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this
end _root_.GlobalTheory.AdLat
end GlobalTheory.AdLat
