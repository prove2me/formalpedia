-- Prove2me | solution 1 for N25.exists_kernel_inclusion_of_character
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:47.647385+00:00
-- url     : https://prove2.me/submissions/88aece42-508a-4bde-9c3b-f16bdbc07737

import Definitions.Def_N25_GlobalKummer

set_option autoImplicit false

noncomputable section

namespace N25

local instance prime71_N25_exists_kernel_inclusion_of_character_sdf1557 : Fact (Nat.Prime 71) :=
  ⟨by decide⟩

/-- A nonzero seventy-one torsion vector with the Fricke cusp eigenvalue and
character determines the required injection into the literal kernel. -/
theorem _root_.solution (hPhi : PhiFiveZero)
    (a : J) (ha : a ≠ 0) (ha71 : 71 • a = 0)
    (hgamma : gamma a = 57 • a)
    (hgal : ∀ σ : Gal, σ • a = (psi σ : ZMod 71).val • a) :
    ∃ i : ZMod 71 →+ ↥V, Function.Injective i ∧ (i 1 : J) = a ∧
      ∀ (σ : Gal) (t : ZMod 71), vAct σ (i t) = i ((psi σ : ZMod 71) * t) := by
  let := GlobalKummer.vModule hPhi
  have hpi : piEnd a = 0 := by
    have hz := congrArg (fun x : J => (49 : ℕ) • x) ha71
    simp only [smul_zero, smul_smul] at hz
    have hcoef : (2 + 4 * 57 + 57 * 57 : ℕ) = 49 * 71 := by norm_num
    simpa only [piEnd, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
      AddMonoidHom.id_apply, AddMonoidHom.comp_apply, hgamma, map_nsmul,
      smul_smul, ← add_nsmul, hcoef] using hz
  let v : ↥V := ⟨a, hpi⟩
  have hv : v ≠ 0 := fun h => ha (congrArg (fun x : ↥V => (x : J)) h)
  let i : ZMod 71 →ₗ[ZMod 71] ↥V := LinearMap.toSpanSingleton (ZMod 71) ↥V v
  have hact (σ : Gal) : vAct σ v = (psi σ : ZMod 71) • v := by
    apply Subtype.ext
    rw [← ZMod.natCast_zmod_val (psi σ : ZMod 71)]
    change σ • a = (((psi σ : ZMod 71).val : ZMod 71) • v : ↥V).val
    rw [Nat.cast_smul_eq_nsmul]
    exact hgal σ
  refine ⟨i.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro s t h
    have hz : (s - t) • v = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)
  · change ((1 : ZMod 71) • v : ↥V).val = a
    rw [one_smul]
  · intro σ t
    change σ • (t • v) = ((psi σ : ZMod 71) * t) • v
    have hs := ZMod.map_smul (DistribSMul.toAddMonoidHom ↥V σ) t v
    change σ • (t • v) = t • (σ • v) at hs
    rw [hs]
    change t • vAct σ v = ((psi σ : ZMod 71) * t) • v
    rw [hact σ, smul_smul, mul_comm]

end N25
