-- Prove2me | solution 1 for GlobalTheory.Pat.PhiFin.finite_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:56.477311+00:00
-- url     : https://prove2.me/submissions/1d90c050-25b4-4aba-9481-1d663d86b61c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
namespace PhiFin
theorem _root_.solution {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (hG : PhiFin l G) {M : Type} [AddCommGroup M] [Finite M]
    (hl : ∀ m : M, l • m = 0) (H : Subgroup G) (hH : IsOpen (H : Set G)) (L R : G → M → M)
    (hL : ∀ h ∈ H, ∀ m, L h m = m) (hR : ∀ h ∈ H, ∀ m, R h m = m) :
    {f : G → M | IsLocallyConstant f ∧ ∀ g h, f (g * h) = L g (f h) + R h (f g)}.Finite := by
  obtain ⟨_⟩ : Nonempty (Module (ZMod l) M) := ⟨AddCommGroup.zmodModule hl⟩
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : Finite (Module.Dual (ZMod l) M) :=
    Finite.of_injective (fun (φ : Module.Dual (ZMod l) M) (m : M) => φ m) fun _ _ e => LinearMap.ext (congrFun e)
  haveI := (hG H hH).to_subtype
  rw [← Set.finite_coe_iff]
  let res : {f : G → M | IsLocallyConstant f ∧ ∀ g h, f (g * h) = L g (f h) + R h (f g)} →
      Module.Dual (ZMod l) M → (H →* Multiplicative (ZMod l)) := fun f φ =>
    MonoidHom.mk' (fun h => Multiplicative.ofAdd (φ (f.1 h))) (fun a b => by
      rw [Subgroup.coe_mul, f.2.2, hL _ a.2, hR _ b.2, map_add, add_comm, ofAdd_add])
  have hres : ∀ f φ, IsOpen ((res f φ).ker : Set H) := fun f φ =>
    ((f.2.1.comp fun m => Multiplicative.ofAdd (φ m)).comp_continuous continuous_subtype_val).isOpen_fiber 1
  refine Finite.of_injective (β := (Module.Dual (ZMod l) M →
      {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}) × (G ⧸ H → M))
    (fun f => (fun φ => ⟨res f φ, hres f φ⟩, fun q => f.1 q.out)) ?_
  intro f g e
  obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
  have h1 : ∀ h : H, f.1 h = g.1 h := fun h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
    intro φ
    have := DFunLike.congr_fun (congrArg Subtype.val (congrFun e1 φ)) h
    rw [map_sub, sub_eq_zero]
    exact Multiplicative.ofAdd.injective this
  ext x
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H x
  have hx : x = (QuotientGroup.mk x : G ⧸ H).out * (h⁻¹ : H) := by rw [hh]; simp
  have h2 : f.1 (QuotientGroup.mk x : G ⧸ H).out = g.1 (QuotientGroup.mk x : G ⧸ H).out := congrFun e2 _
  rw [hx, f.2.2, g.2.2, h1, h2]
end PhiFin
end GlobalTheory.Pat
