-- Prove2me | solution 1 for MazurAdmissible.filtAlpha_eq_filtAlpha
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c527fbc5-f280-5799-96a6-220fb624bfcd

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha

set_option autoImplicit false

noncomputable section

namespace MazurAdmissible
p2m_export "MazurAdmissible" "OpenAction IsTrivialStep IsCyclotomicStep AdmissibleChain filtAlpha filtLength"
p2m_open "MazurAdmissible"

variable {M : Type*} [AddCommGroup M]
local notation "Qbar" => AlgebraicClosure ℚ

section JH

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace OpenAction p2m_export "MazurAdmissible.OpenAction" "φ mk" end OpenAction
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private def _root_.MazurAdmissible.OpenAction.toRep (Φ : OpenAction M) : Representation ℤ Gal M where
  toFun σ := (Φ.φ σ : M ≃+ M).toAddMonoidHom.toIntLinearMap
  map_one' := by
    ext x
    show Φ.φ 1 x = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    ext x
    show Φ.φ (σ * τ) x = Φ.φ σ (Φ.φ τ x)

    have h := congrArg (fun e : AddAut M => e x) (map_mul Φ.φ σ τ)
    exact h.trans rfl

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.toRep"
p2m_open_scoped "MazurAdmissible.OpenAction" in
@[scoped simp] theorem OpenAction.toRep_apply (Φ : OpenAction M) (σ : Gal) (x : M) :
    Φ.toRep σ x = Φ.φ σ x := rfl

p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction"
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private def _root_.MazurAdmissible.OpenAction.V (Φ : OpenAction M) : Type _ := M

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.V"
p2m_open_scoped "MazurAdmissible.OpenAction" in
scoped instance OpenAction.instAddCommGroupV (Φ : OpenAction M) : AddCommGroup Φ.V :=
  inferInstanceAs (AddCommGroup M)

p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction"
p2m_open_scoped "MazurAdmissible.OpenAction" in
noncomputable scoped instance OpenAction.instModuleV (Φ : OpenAction M) : Module (MonoidAlgebra ℤ Gal) Φ.V :=
  Module.compHom M Φ.toRep.asAlgebraHom.toRingHom

p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction"
p2m_open_scoped "MazurAdmissible.OpenAction" in
theorem OpenAction.smul_def (Φ : OpenAction M) (r : MonoidAlgebra ℤ Gal) (v : Φ.V) :
    r • v = (Φ.toRep.asAlgebraHom r (show M from v) : M) := rfl

p2m_open_scoped "MazurAdmissible.OpenAction" in
theorem OpenAction.of_smul (Φ : OpenAction M) (g : Gal) (v : Φ.V) :
    MonoidAlgebra.of ℤ Gal g • v = (Φ.φ g (show M from v) : M) := by
  rw [OpenAction.smul_def, Representation.asAlgebraHom_of, OpenAction.toRep_apply]

namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private def _root_.MazurAdmissible.OpenAction.toSub (Φ : OpenAction M) (S : AddSubgroup M)
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) : Submodule (MonoidAlgebra ℤ Gal) Φ.V where
  carrier := (S : Set M)
  add_mem' {a b} ha hb := S.add_mem ha hb
  zero_mem' := S.zero_mem
  smul_mem' r v hv := by
    change (show M from v) ∈ S at hv
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [OpenAction.of_smul]; exact hS g _ hv
    | add x y hx hy => rw [add_smul]; exact S.add_mem hx hy
    | smul r x hx =>
        rw [OpenAction.smul_def, map_smul, LinearMap.smul_apply, ← OpenAction.smul_def]
        exact S.zsmul_mem hx r

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.toSub"
p2m_open_scoped "MazurAdmissible.OpenAction" in
theorem OpenAction.mem_toSub (Φ : OpenAction M) (S : AddSubgroup M)
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) (v : Φ.V) :
    v ∈ Φ.toSub S hS ↔ (show M from v) ∈ S := Iff.rfl

p2m_open_scoped "MazurAdmissible.OpenAction" in
theorem OpenAction.toSub_toAddSubgroup (Φ : OpenAction M) (S : AddSubgroup M)
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) :
    (Φ.toSub S hS).toAddSubgroup = S := SetLike.coe_injective rfl

namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in
private theorem _root_.MazurAdmissible.OpenAction.toSub_mono (Φ : OpenAction M) {S T : AddSubgroup M}
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) (hT : ∀ σ : Gal, ∀ x ∈ T, Φ.φ σ x ∈ T) (h : S ≤ T) :
    Φ.toSub S hS ≤ Φ.toSub T hT := fun _ hv => h hv

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.toSub_mono"
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in
private theorem _root_.MazurAdmissible.OpenAction.toSub_congr (Φ : OpenAction M) {S T : AddSubgroup M}
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) (hT : ∀ σ : Gal, ∀ x ∈ T, Φ.φ σ x ∈ T) (h : S = T) :
    Φ.toSub S hS = Φ.toSub T hT := by
  subst h; rfl

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.toSub_congr"
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private theorem _root_.MazurAdmissible.OpenAction.natCard_toSub_quot (Φ : OpenAction M) {S T : AddSubgroup M}
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) (hT : ∀ σ : Gal, ∀ x ∈ T, Φ.φ σ x ∈ T) :
    Nat.card (↥(Φ.toSub T hT) ⧸ Submodule.comap (Φ.toSub T hT).subtype (Φ.toSub S hS)) =
      Nat.card (↥T ⧸ S.addSubgroupOf T) := by
  show (Φ.toSub S hS).toAddSubgroup.relIndex (Φ.toSub T hT).toAddSubgroup = S.relIndex T
  rw [OpenAction.toSub_toAddSubgroup, OpenAction.toSub_toAddSubgroup]
  rfl

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.natCard_toSub_quot"

theorem isSimpleModule_of_natCard_prime {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    {q : ℕ} (hq : q.Prime) (h : Nat.card N = q) : IsSimpleModule R N := by
  haveI : Finite N := Nat.finite_of_card_ne_zero (h ▸ hq.ne_zero)
  haveI : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hq.one_lt)
  have key : ∀ P : Submodule R N, P = ⊥ ∨ P = ⊤ := fun P => by
    have hdvd : Nat.card P ∣ q := h ▸ P.toAddSubgroup.card_addSubgroup_dvd_card
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hP
    · left
      rw [eq_bot_iff]
      intro x hx
      have hs : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
      have : (⟨x, hx⟩ : P) = 0 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val this
    · right
      apply Submodule.toAddSubgroup_injective
      rw [Submodule.top_toAddSubgroup]
      exact AddSubgroup.eq_top_of_card_eq _ (hP.trans h.symm)
  haveI : IsSimpleOrder (Submodule R N) := ⟨key⟩
  exact ⟨⟩

namespace AdmissibleChain p2m_export "MazurAdmissible.AdmissibleChain" "tag hmono step n mk hact htop hbot hcard" end AdmissibleChain
namespace AdmissibleChain
p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

private theorem _root_.MazurAdmissible.AdmissibleChain.step_stable {q : ℕ} (hq : q.Prime) {Φ : OpenAction M} (c : AdmissibleChain q Φ)
    (i : Fin (c.n + 1)) : ∀ σ : Gal, ∀ x ∈ c.step i, Φ.φ σ x ∈ c.step i := by
  haveI : Fact q.Prime := ⟨hq⟩
  induction i using Fin.induction with
  | zero => intro σ x hx; rw [c.hbot] at hx ⊢; rw [AddSubgroup.mem_bot] at hx; subst hx; simp
  | succ i _ =>
    intro σ x hx
    have hact := c.hact i
    by_cases htag : c.tag i = true
    · rw [if_pos htag] at hact
      have h := hact σ x hx
      have := (c.step i.succ).add_mem (c.hmono i h) hx
      rwa [sub_add_cancel] at this
    · rw [if_neg htag] at hact
      obtain ⟨ζ, hζ⟩ : ∃ ζ : Qbar, IsPrimitiveRoot ζ q := by
        obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Qbar) (by
          rw [Polynomial.degree_cyclotomic]
          exact_mod_cast (Nat.totient_pos.mpr hq.pos).ne')
        exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
      obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
      have h := hact σ ζ hζ a ha.symm x hx
      have := (c.step i.succ).add_mem (c.hmono i h) ((c.step i.succ).nsmul_mem hx a)
      rwa [sub_add_cancel] at this

end AdmissibleChain
p2m_export "MazurAdmissible" "AdmissibleChain.step_stable"
namespace AdmissibleChain
p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

private def _root_.MazurAdmissible.AdmissibleChain.toCompositionSeries {q : ℕ} (hq : q.Prime) {Φ : OpenAction M} (c : AdmissibleChain q Φ) :
    CompositionSeries (Submodule (MonoidAlgebra ℤ Gal) Φ.V) where
  length := c.n
  toFun i := Φ.toSub (c.step i) (c.step_stable hq i)
  step i := by
    show Φ.toSub (c.step i.castSucc) (c.step_stable hq _) ⋖ Φ.toSub (c.step i.succ) (c.step_stable hq _)
    rw [covBy_iff_quot_is_simple (Φ.toSub_mono _ _ (c.hmono i))]
    exact isSimpleModule_of_natCard_prime hq ((Φ.natCard_toSub_quot _ _).trans (c.hcard i))

end AdmissibleChain
p2m_export "MazurAdmissible" "AdmissibleChain.toCompositionSeries"

def TrivQuot (Φ : OpenAction M) (X Y : Submodule (MonoidAlgebra ℤ Gal) Φ.V) : Prop :=
  ∀ g : Gal, ∀ v ∈ Y, MonoidAlgebra.of ℤ Gal g • v - v ∈ X

theorem trivQuot_toSub_iff (Φ : OpenAction M) {S T : AddSubgroup M}
    (hS : ∀ σ : Gal, ∀ x ∈ S, Φ.φ σ x ∈ S) (hT : ∀ σ : Gal, ∀ x ∈ T, Φ.φ σ x ∈ T) :
    TrivQuot Φ (Φ.toSub S hS) (Φ.toSub T hT) ↔ IsTrivialStep Φ S T := by
  constructor
  · intro h σ x hx
    have h' := h σ x hx
    rw [OpenAction.of_smul] at h'
    exact h'
  · intro h g v hv
    rw [OpenAction.of_smul]
    exact h g _ hv

theorem trivQuot_iff_quotient (Φ : OpenAction M) {X Y : Submodule (MonoidAlgebra ℤ Gal) Φ.V} :
    TrivQuot Φ X Y ↔ ∀ g : Gal, ∀ z : ↥Y ⧸ Submodule.comap Y.subtype X,
      MonoidAlgebra.of ℤ Gal g • z = z := by
  constructor
  · intro h g z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul]
    have := X.neg_mem (h g y y.2)
    rwa [neg_sub] at this
  · intro h g v hv
    have h' := h g (Submodule.Quotient.mk ⟨v, hv⟩)
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul] at h'
    have := X.neg_mem h'
    rwa [neg_sub] at this

theorem trivQuot_iff_of_iso (Φ : OpenAction M) {X₁ Y₁ X₂ Y₂ : Submodule (MonoidAlgebra ℤ Gal) Φ.V}
    (h : JordanHolderLattice.Iso (X₁, Y₁) (X₂, Y₂)) : TrivQuot Φ X₁ Y₁ ↔ TrivQuot Φ X₂ Y₂ := by
  obtain ⟨e⟩ : Nonempty ((↥Y₁ ⧸ Submodule.comap Y₁.subtype X₁) ≃ₗ[MonoidAlgebra ℤ Gal]
      (↥Y₂ ⧸ Submodule.comap Y₂.subtype X₂)) := ⟨JordanHolderLattice.Iso.linearEquiv h⟩
  rw [trivQuot_iff_quotient, trivQuot_iff_quotient]
  constructor
  · intro H g z
    apply e.symm.injective
    rw [LinearEquiv.map_smul]
    exact H g (e.symm z)
  · intro H g z
    apply e.injective
    rw [LinearEquiv.map_smul]
    exact H g (e z)

end JH
p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction"

section Splice

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {q : ℕ} {Φ : OpenAction M} {N : AddSubgroup M}
  {ΦN : OpenAction ↥N} {ΦQ : OpenAction (M ⧸ N)}
  (cN : AdmissibleChain q ΦN) (cQ : AdmissibleChain q ΦQ)

def spliceStep (i : Fin (cN.n + cQ.n + 1)) : AddSubgroup M :=
  if h : (i : ℕ) ≤ cN.n then (cN.step ⟨i, by omega⟩).map N.subtype
  else (cQ.step ⟨i - cN.n, by omega⟩).comap (QuotientAddGroup.mk' N)

def spliceTag (i : Fin (cN.n + cQ.n)) : Bool :=
  if h : (i : ℕ) + 1 ≤ cN.n then cN.tag ⟨i, by omega⟩ else cQ.tag ⟨i - cN.n, by omega⟩

variable {cN cQ}

theorem spliceStep_of_le (i : Fin (cN.n + cQ.n + 1)) (h : (i : ℕ) ≤ cN.n) :
    spliceStep cN cQ i = (cN.step ⟨i, by omega⟩).map N.subtype := by
  rw [spliceStep, dif_pos h]

theorem spliceStep_of_ge (i : Fin (cN.n + cQ.n + 1)) (h : cN.n ≤ (i : ℕ)) :
    spliceStep cN cQ i = (cQ.step ⟨i - cN.n, by omega⟩).comap (QuotientAddGroup.mk' N) := by
  by_cases h' : (i : ℕ) ≤ cN.n
  ·
    have hi : (i : ℕ) = cN.n := le_antisymm h' h
    rw [spliceStep, dif_pos h']
    have h1 : (⟨i, by omega⟩ : Fin (cN.n + 1)) = Fin.last cN.n := Fin.ext hi
    have h2 : (⟨i - cN.n, by omega⟩ : Fin (cQ.n + 1)) = 0 := Fin.ext (by simp [hi])
    rw [h1, h2, cN.htop, cQ.hbot, AddMonoidHom.comap_bot, QuotientAddGroup.ker_mk',
      ← AddMonoidHom.range_eq_map, AddSubgroup.range_subtype]
  · rw [spliceStep, dif_neg h']

theorem relIndex_spliceStep (hq : q.Prime) (i : Fin (cN.n + cQ.n)) :
    (spliceStep cN cQ i.castSucc).relIndex (spliceStep cN cQ i.succ) = q := by
  by_cases h : (i : ℕ) + 1 ≤ cN.n
  · rw [spliceStep_of_le i.castSucc (by simp; omega), spliceStep_of_le i.succ (by simpa using h),
      ← AddSubgroup.relIndex_comap,
      AddSubgroup.comap_map_eq_self_of_injective N.subtype_injective]
    have := cN.hcard ⟨i, by omega⟩
    exact this
  · rw [not_le] at h
    rw [spliceStep_of_ge i.castSucc (by simp; omega), spliceStep_of_ge i.succ (by simp; omega),
      AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective N)]
    have e1 : (⟨i - cN.n, by omega⟩ : Fin cQ.n).castSucc = ⟨(i.castSucc : ℕ) - cN.n, by simp; omega⟩ :=
      Fin.ext (by simp)
    have e2 : (⟨i - cN.n, by omega⟩ : Fin cQ.n).succ = ⟨(i.succ : ℕ) - cN.n, by simp; omega⟩ :=
      Fin.ext (by simp; omega)
    have := cQ.hcard ⟨i - cN.n, by omega⟩
    rw [e1, e2] at this
    exact this

end Splice
p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction"

section Splice2

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {q : ℕ} {Φ : OpenAction M} {N : AddSubgroup M}
  {ΦN : OpenAction ↥N} {ΦQ : OpenAction (M ⧸ N)}

theorem isTrivialStep_map (hΦN : ∀ (σ : Gal) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    {A B : AddSubgroup ↥N} (h : IsTrivialStep ΦN A B) :
    IsTrivialStep Φ (A.map N.subtype) (B.map N.subtype) := by
  intro σ x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hx
  refine AddSubgroup.mem_map.mpr ⟨ΦN.φ σ y - y, h σ y hy, ?_⟩
  simp [hΦN]

theorem isCyclotomicStep_map (hΦN : ∀ (σ : Gal) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    {A B : AddSubgroup ↥N} (h : IsCyclotomicStep q ΦN A B) :
    IsCyclotomicStep q Φ (A.map N.subtype) (B.map N.subtype) := by
  intro σ ζ hζ a ha x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hx
  refine AddSubgroup.mem_map.mpr ⟨ΦN.φ σ y - a • y, h σ ζ hζ a ha y hy, ?_⟩
  simp [hΦN]

theorem isTrivialStep_comap
    (hΦQ : ∀ (σ : Gal) (x : M), ΦQ.φ σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ.φ σ x))
    {A B : AddSubgroup (M ⧸ N)} (h : IsTrivialStep ΦQ A B) :
    IsTrivialStep Φ (A.comap (QuotientAddGroup.mk' N)) (B.comap (QuotientAddGroup.mk' N)) := by
  intro σ x hx
  rw [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply] at hx ⊢
  have := h σ _ hx
  rwa [hΦQ, ← QuotientAddGroup.mk_sub] at this

theorem isCyclotomicStep_comap
    (hΦQ : ∀ (σ : Gal) (x : M), ΦQ.φ σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ.φ σ x))
    {A B : AddSubgroup (M ⧸ N)} (h : IsCyclotomicStep q ΦQ A B) :
    IsCyclotomicStep q Φ (A.comap (QuotientAddGroup.mk' N)) (B.comap (QuotientAddGroup.mk' N)) := by
  intro σ ζ hζ a ha x hx
  rw [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply] at hx ⊢
  have := h σ ζ hζ a ha _ hx
  rwa [hΦQ, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_sub] at this

variable (hq : q.Prime)
  (hΦN : ∀ (σ : Gal) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
  (hΦQ : ∀ (σ : Gal) (x : M), ΦQ.φ σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ.φ σ x))
  (cN : AdmissibleChain q ΦN) (cQ : AdmissibleChain q ΦQ)

def spliceChain : AdmissibleChain q Φ where
  n := cN.n + cQ.n
  step := spliceStep cN cQ
  hbot := by
    rw [spliceStep_of_le _ (Nat.zero_le _)]
    have : (⟨((0 : Fin (cN.n + cQ.n + 1)) : ℕ), by simp⟩ : Fin (cN.n + 1)) = 0 := Fin.ext rfl
    rw [this, cN.hbot, AddSubgroup.map_bot]
  htop := by
    rw [spliceStep_of_ge _ (by simp)]
    have : (⟨((Fin.last (cN.n + cQ.n)) : ℕ) - cN.n, by simp⟩ : Fin (cQ.n + 1)) = Fin.last cQ.n :=
      Fin.ext (by simp)
    rw [this, cQ.htop, AddSubgroup.comap_top]
  hmono i := by
    by_cases h : (i : ℕ) + 1 ≤ cN.n
    · rw [spliceStep_of_le i.castSucc (by simp; omega), spliceStep_of_le i.succ (by simpa using h)]
      exact AddSubgroup.map_mono (by
        have := cN.hmono ⟨i, by omega⟩
        exact this)
    · rw [not_le] at h
      rw [spliceStep_of_ge i.castSucc (by simp; omega), spliceStep_of_ge i.succ (by simp; omega)]
      refine AddSubgroup.comap_mono ?_
      have := cQ.hmono ⟨i - cN.n, by omega⟩
      convert this using 2 <;> simp <;> omega
  tag := spliceTag cN cQ
  hcard i := relIndex_spliceStep hq i
  hact i := by
    by_cases h : (i : ℕ) + 1 ≤ cN.n
    · rw [spliceTag, dif_pos h, spliceStep_of_le i.castSucc (by simp; omega),
        spliceStep_of_le i.succ (by simpa using h)]
      have hact := cN.hact ⟨i, by omega⟩
      split_ifs with ht
      · rw [if_pos ht] at hact; exact isTrivialStep_map hΦN hact
      · rw [if_neg ht] at hact; exact isCyclotomicStep_map hΦN hact
    · rw [not_le] at h
      rw [spliceTag, dif_neg (by omega), spliceStep_of_ge i.castSucc (by simp; omega),
        spliceStep_of_ge i.succ (by simp; omega)]
      have hact := cQ.hact ⟨i - cN.n, by omega⟩
      have e1 : (⟨i - cN.n, by omega⟩ : Fin cQ.n).castSucc = ⟨(i.castSucc : ℕ) - cN.n, by simp; omega⟩ :=
        Fin.ext (by simp)
      have e2 : (⟨i - cN.n, by omega⟩ : Fin cQ.n).succ = ⟨(i.succ : ℕ) - cN.n, by simp; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e1, e2] at hact
      split_ifs with ht
      · rw [if_pos ht] at hact; exact isTrivialStep_comap hΦQ hact
      · rw [if_neg ht] at hact; exact isCyclotomicStep_comap hΦQ hact

theorem filtLength_spliceChain : filtLength (spliceChain hq hΦN hΦQ cN cQ) = filtLength cN + filtLength cQ :=
  rfl

theorem filtAlpha_spliceChain :
    filtAlpha (spliceChain hq hΦN hΦQ cN cQ) = filtAlpha cN + filtAlpha cQ := by
  classical
  unfold filtAlpha
  simp only [Finset.card_filter]
  show (∑ i : Fin (cN.n + cQ.n), if spliceTag cN cQ i = true then 1 else 0) = _
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h : ((Fin.castAdd cQ.n i : Fin (cN.n + cQ.n)) : ℕ) + 1 ≤ cN.n := by
      rw [Fin.val_castAdd]; exact i.2
    rw [spliceTag, dif_pos h]
    rcases i with ⟨i, hi⟩
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h : ¬ ((Fin.natAdd cN.n j : Fin (cN.n + cQ.n)) : ℕ) + 1 ≤ cN.n := by simp
    rw [spliceTag, dif_neg h]
    have : (⟨((Fin.natAdd cN.n j : Fin (cN.n + cQ.n)) : ℕ) - cN.n, by simp⟩ : Fin cQ.n) = j :=
      Fin.ext (by simp)
    rw [this]

end Splice2
p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction"

theorem not_isTrivialStep_of_isCyclotomicStep {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (Φ : OpenAction M) {A B : AddSubgroup M} (hAB : A ≤ B)
    (hcard : Nat.card (↥B ⧸ A.addSubgroupOf B) = q)
    (hcyc : IsCyclotomicStep q Φ A B) : ¬ IsTrivialStep Φ A B := by
  intro htriv
  haveI : Fact q.Prime := ⟨hq⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Qbar, IsPrimitiveRoot ζ q := by
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Qbar) (by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr hq.pos).ne')
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) q :=
    hζ.pow_of_coprime 2 ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm)
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  haveI : Normal ℚ Qbar := ⟨fun x => IsAlgClosed.splits _⟩
  have hirr := Polynomial.cyclotomic.irreducible_rat hq.pos
  have hmin : minpoly ℚ (ζ ^ 2) = minpoly ℚ ζ := by
    rw [← hζ2.minpoly_eq_cyclotomic_of_irreducible hirr, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr]
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp ((Normal.minpoly_eq_iff_mem_orbit Qbar).mp hmin)

  have hσ' : σ ζ = ζ ^ 2 := hσ

  have hBA : B ≤ A := fun x hx => by
    have h1 := htriv σ x hx
    have h2 := hcyc σ ζ hζ 2 hσ' x hx
    have h3 := A.sub_mem h1 h2
    rwa [sub_sub_sub_cancel_left, two_nsmul, add_sub_cancel_right] at h3

  have hidx : (A.addSubgroupOf B).index = q := hcard
  rw [AddSubgroup.addSubgroupOf_eq_top.mpr hBA, AddSubgroup.index_top] at hidx
  exact hq.one_lt.ne hidx

end MazurAdmissible
p2m_reactivate "P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible.OpenAction P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible"

p2m_open "MazurAdmissible P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.MazurAdmissible"

theorem solution
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Φ : OpenAction M}
    (c c' : AdmissibleChain q Φ) : filtAlpha c = filtAlpha c' := by
  classical
  have hhead : (c.toCompositionSeries hq).head = (c'.toCompositionSeries hq).head := by
    show Φ.toSub (c.step 0) (c.step_stable hq 0) = Φ.toSub (c'.step 0) (c'.step_stable hq 0)
    exact Φ.toSub_congr _ _ (c.hbot.trans c'.hbot.symm)
  have hlast : (c.toCompositionSeries hq).last = (c'.toCompositionSeries hq).last := by
    show Φ.toSub (c.step (Fin.last c.n)) (c.step_stable hq _) =
      Φ.toSub (c'.step (Fin.last c'.n)) (c'.step_stable hq _)
    exact Φ.toSub_congr _ _ (c.htop.trans c'.htop.symm)
  obtain ⟨f, hf⟩ := CompositionSeries.jordan_holder _ _ hhead hlast

  have key : ∀ (d : AdmissibleChain q Φ) (i : Fin d.n), d.tag i = true ↔
      TrivQuot Φ (Φ.toSub (d.step i.castSucc) (d.step_stable hq _))
        (Φ.toSub (d.step i.succ) (d.step_stable hq _)) := by
    intro d i
    rw [trivQuot_toSub_iff]
    have hact := d.hact i
    constructor
    · intro ht; rwa [if_pos ht] at hact
    · intro htriv
      by_contra ht
      rw [if_neg ht] at hact
      exact not_isTrivialStep_of_isCyclotomicStep hq hq2 Φ (d.hmono i) (d.hcard i) hact htriv
  unfold filtAlpha
  refine Finset.card_equiv f fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (key c i).trans ((trivQuot_iff_of_iso Φ (hf i)).trans (key c' (f i)).symm)

end
end S_MazurAdmissible_filtAlpha_eq_filtAlpha
end P2MW
export P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha (solution)
