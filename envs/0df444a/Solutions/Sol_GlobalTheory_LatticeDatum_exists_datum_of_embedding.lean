-- Prove2me | solution 1 for GlobalTheory.LatticeDatum.exists_datum_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:40.302165+00:00
-- url     : https://prove2.me/submissions/27876b3a-f229-47d0-aa5b-48a22aa08c16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
import Theorems.Thm_GlobalTheory_LatticeDatum_exists_factor
import Theorems.Thm_GlobalTheory_LatticeDatum_transport_complexStructure
import Theorems.Thm_GlobalTheory_HermModel_finrank_eq_of_injective_of_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.LatticeDatum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.LatticeDatum
theorem _root_.solution (H : Host E) (D : Datum H) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hinj : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ x) (φ y))
    (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L]
    (φ' : L →ₗ[𝓞 E] (Fin r → E)) (hinj' : Function.Injective φ')
    (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (hdual : ∀ v, (∀ y, ∃ n : ℤ, traceHerm ξ Gm v (φ' y) = n) ↔ v ∈ LinearMap.range φ') :
    ∃ (D' : Datum H) (φ'' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧
      LinearMap.range φ'' = LinearMap.range φ' ∧ Function.Injective φ'' ∧
      ∀ x y, ((D'.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ'' x) (φ'' y) := by
  haveI := D.fin
  obtain ⟨N, ψ, hN, hψ⟩ := exists_factor φ φ' hinj hspan
  obtain ⟨M, χ, hM, hχ⟩ := exists_factor φ' φ hinj' hspan'
  have h1 : ∀ x, ψ (χ x) = (N * M) • x := fun x => hinj (by rw [hψ, hχ, map_nsmul, mul_smul])
  have h2 : ∀ x, χ (ψ x) = (N * M) • x := fun x => hinj' (by
    rw [hχ, hψ, map_nsmul, mul_comm, mul_smul])
  choose n hn using fun x : L => (hdual (φ' x)).mpr ⟨x, rfl⟩
  have hl : ∀ x x' y, n (x + x') y = n x y + n x' y := fun x x' y => by
    have := hn (x + x') y
    rw [map_add, map_add, AddMonoidHom.add_apply, hn, hn] at this
    exact_mod_cast this.symm
  have hr : ∀ x y y', n x (y + y') = n x y + n x y' := fun x y y' => by
    have := hn x (y + y')
    rw [map_add, map_add, hn, hn] at this
    exact_mod_cast this.symm
  let B : LinearMap.BilinForm ℤ L :=
    (AddMonoidHom.mk' (fun x => (AddMonoidHom.mk' (n x) (hr x)).toIntLinearMap)
      fun x x' => LinearMap.ext fun y => hl x x' y).toIntLinearMap
  have hB : ∀ x y, ((B x y : ℤ) : ℚ) = traceHerm ξ Gm (φ' x) (φ' y) := fun x y => (hn x y).symm
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hNN : ((N * N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hN hN).ne'
  have hsc : ∀ x y, D.EF (ψ x) (ψ y) = (N * N : ℕ) * B x y := fun x y => by
    have := hEF (ψ x) (ψ y)
    rw [hψ, hψ, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, ← hB, nsmul_eq_mul, nsmul_eq_mul,
      ← mul_assoc] at this
    exact_mod_cast this
  have hmix : ∀ x y, (N : ℤ) * B x (χ y) = M * D.EF (ψ x) y := fun x y => by
    have e1 := hEF (ψ x) y
    have e2 := hB x (χ y)
    rw [hψ, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul] at e1
    rw [hχ, map_nsmul, nsmul_eq_mul] at e2
    have : (N : ℚ) * (B x (χ y) : ℤ) = M * (D.EF (ψ x) y : ℤ) := by rw [e1, e2]; ring
    exact_mod_cast this
  have hbij : Function.Bijective B := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h0 : ψ x = 0 := by
        apply D.unimod.1
        ext y
        have := hmix x y
        rw [hx, LinearMap.zero_apply, mul_zero] at this
        have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
        rw [(mul_eq_zero.mp this.symm).resolve_left hMZ, map_zero, LinearMap.zero_apply]
      have h3 := hψ x
      rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at h3
      exact hinj' (by rw [map_zero]; exact (smul_eq_zero.mp h3.symm).resolve_left hNQ)
    · intro f
      obtain ⟨x, hx⟩ := D.unimod.2 (f ∘ₗ χ.toAddMonoidHom.toIntLinearMap)
      have hx' : ∀ y, D.EF x y = f (χ y) := fun y => by rw [hx]; rfl
      have hv : ∀ z, traceHerm ξ Gm ((M : ℚ)⁻¹ • φ x) (φ' z) = f z := fun z => by
        have e1 := hEF x (ψ z)
        rw [hx', h2, map_nsmul, hψ, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at e1
        push_cast at e1
        have e2 : traceHerm ξ Gm (φ x) (φ' z) = M * traceHerm ξ Gm ((M : ℚ)⁻¹ • φ x) (φ' z) := by
          rw [← nsmul_eq_mul, ← AddMonoidHom.nsmul_apply, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
            mul_inv_cancel₀ hMQ, one_smul]
        rw [e2, ← mul_assoc] at e1
        exact (mul_left_cancel₀ (mul_ne_zero hNQ hMQ) e1).symm
      obtain ⟨w, hw⟩ := (hdual _).mp fun z => ⟨f z, hv z⟩
      refine ⟨w, LinearMap.ext fun z => ?_⟩
      have := hB w z
      rw [hw, hv] at this
      exact_mod_cast this
  haveI : Module.IsTorsionFree (𝓞 E) L := Function.Injective.moduleIsTorsionFree φ' hinj' (map_smul φ')
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  refine ⟨{ La := L, fin := inferInstance, proj := hproj, EF := B, alt := fun x => ?_, unimod := hbij,
            adj := fun a x y => ?_, p := D.p, q := D.q, rank := ?_, dom := ?_ }, φ', rfl, rfl, rfl, hinj', hB⟩
  · apply mul_left_cancel₀ hNN
    rw [← hsc, D.alt, mul_zero]
  · apply mul_left_cancel₀ hNN
    rw [← hsc, ← hsc, map_smul ψ, map_smul ψ, D.adj]
  · rw [← D.rank, HermModel.finrank_eq_of_injective_of_span (K := E) φ hinj hspan,
      HermModel.finrank_eq_of_injective_of_span (K := E) φ' hinj' hspan']
  · exact transport_complexStructure D.EF B ψ χ (N * M) (N * N) (Nat.mul_pos hN hM) (Nat.mul_pos hN hN)
      h1 h2 hsc _ D.dom
end GlobalTheory.LatticeDatum
